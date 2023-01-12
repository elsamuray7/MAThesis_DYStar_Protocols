module OYRS.Protocol


let initiator_init a srv b =
  let (|i,k_as|) = rand_gen #oyrs_preds (readers [P a; P srv]) (aead_usage "sk_i_srv") in
  let new_sess_idx = new_session_number #oyrs_preds a in
  let st_i_init = InitiatorInit srv k_as b in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now a new_sess_idx 0 st_i_init in
  new_session #oyrs_preds #now a new_sess_idx 0 ser_st;
  ((|i,k_as|), new_sess_idx)

let responder_init b srv =
  let (|i,k_bs|) = rand_gen #oyrs_preds (readers [P b; P srv]) (aead_usage "sk_r_srv") in
  let new_sess_idx = new_session_number #oyrs_preds b in
  let st_r_init = ResponderInit srv k_bs in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now b new_sess_idx 0 st_r_init in
  new_session #oyrs_preds #now b new_sess_idx 0 ser_st;
  ((|i,k_bs|), new_sess_idx)

let install_sk_at_auth_server #i srv p sk =
  let new_sess_idx = new_session_number #oyrs_preds srv in
  let st_srv_sess = AuthServerSession p sk in
  let now = global_timestamp () in

  // Prove that sk can flow to srv at now
  can_flow_later i now (readers [P p; P srv]) (readers [P p; P srv]);
  is_valid_later oyrs_global_usage i now sk;
  can_flow_transitive now (get_label oyrs_key_usages sk) (readers [P p; P srv]) (readers [P srv]);
  let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sess in

  new_session #oyrs_preds #now srv new_sess_idx 0 ser_st

let initiator_send_msg_1 a a_si =
  // get initiator session
  let now = global_timestamp () in
  let (|a_vi,ser_st|) = get_session #oyrs_preds #now a a_si in

  match parse_session_st ser_st with
  | Success (InitiatorInit srv k_as b) -> (
    // generate conversation id and initiator nonce
    let (|_,c|) = rand_gen #oyrs_preds public (nonce_usage "conv_id") in
    let (|_,n_a|) = rand_gen #oyrs_preds (readers [P a; P srv]) (nonce_usage "nonce_i") in

    // create and send first message
    let ev1 = EncMsg1 n_a c a b in
    let now = global_timestamp () in
    let ser_ev1 = serialize_encval now ev1 (get_label oyrs_key_usages k_as) in
    let c_ev1 = aead_enc #oyrs_global_usage #now #(get_label oyrs_key_usages k_as) k_as (string_to_bytes #oyrs_global_usage #now "iv") ser_ev1 (string_to_bytes #oyrs_global_usage #now "ev1") in

    let msg1 = Msg1 c a b c_ev1 in
    let now = global_timestamp () in
    let ser_msg1 = serialize_msg now msg1 in

    let send_m1_idx = send #oyrs_preds a b ser_msg1 in

    // update initiator session
    let st_i_m1 = InitiatorSentMsg1 srv k_as b c n_a in
    let now = global_timestamp () in
    let ser_st = serialize_session_st now a a_si a_vi st_i_m1 in
    update_session #oyrs_preds #now a a_si a_vi ser_st;

    send_m1_idx
  )
  | _ -> error "i_send_m1: wrong session"

let responder_send_msg_2 b m1_idx b_si =
  // get responder session
  let now = global_timestamp () in
  let (|b_vi,ser_st|) = get_session #oyrs_preds #now b b_si in

  match parse_session_st ser_st with
  | Success (ResponderInit srv k_bs) -> (
    // receive and parse first message
    let (|_,a,ser_msg1|) = receive_i #oyrs_preds m1_idx b in

    match parse_msg ser_msg1 with
    | Success (Msg1 c a b' c_ev_a) -> (
      if b <> b' then error "r_send_m2: message was intended for different principal"
      else
        // generate responder nonce
        let (|_,n_b|) = rand_gen #oyrs_preds (readers [P b; P srv]) (nonce_usage "nonce_r") in

        // create and send second message
        let ev2 = EncMsg2 n_b c a b in
        let now = global_timestamp () in
        let ser_ev2 = serialize_encval now ev2 (get_label oyrs_key_usages k_bs) in
        let c_ev2 = aead_enc #oyrs_global_usage #now #(get_label oyrs_key_usages k_bs) k_bs (string_to_bytes #oyrs_global_usage #now "iv") ser_ev2 (string_to_bytes #oyrs_global_usage #now "ev2") in

        let c_ev_a:msg oyrs_global_usage now public = c_ev_a in
        let msg2 = Msg2 c a b c_ev_a c_ev2 in
        let now = global_timestamp () in
        let ser_msg2 = serialize_msg now msg2 in

        let send_m2_idx = send #oyrs_preds b srv ser_msg2 in

        // update responder session
        let st_r_m2 = ResponderSentMsg2 srv k_bs a c n_b in
        let now = global_timestamp () in
        let ser_st = serialize_session_st now b b_si b_vi st_r_m2 in
        update_session #oyrs_preds #now b b_si b_vi ser_st;

        send_m2_idx
    )
    | _ -> error "r_send_m2: wrong message"
  )
  | _ -> error "r_send_m2: wrong session"
