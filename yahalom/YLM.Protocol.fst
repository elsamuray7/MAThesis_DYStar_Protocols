module YLM.Protocol


let new_lt_key_session p srv =
  let (|i,k_ps|) = rand_gen #ylm_preds (readers [P p; P srv]) (aead_usage "YLM.lt_key") in

  let new_sess_idx = new_session_number #ylm_preds p in
  let st_key_sess = PKeySession srv k_ps in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now p new_sess_idx 0 st_key_sess in

  new_session #ylm_preds #now p new_sess_idx 0 ser_st;

  print_string ("new long term key session of " ^ p ^ " with " ^ srv ^ "\n");

  ((|i,k_ps|), new_sess_idx)

let install_lt_key_at_auth_server #i srv p k_ps =
  let new_sess_idx = new_session_number #ylm_preds srv in
  let st_srv_sess = AuthServerSession p k_ps in
  let now = global_timestamp () in
  is_valid_later ylm_global_usage i now k_ps;
  assert(can_flow now (get_label ylm_key_usages k_ps) (readers [P srv]));
  let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sess in

  print_string ("installed long term key of " ^ p ^ " at " ^ srv ^ "\n");

  new_session #ylm_preds #now srv new_sess_idx 0 ser_st

let get_lt_key_session (p:principal) (kps_idx:nat) :
  LCrypto (vi:nat & st:session_st) (pki ylm_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 (|vi,st|) t1 -> trace_len t1 == trace_len t0 /\
    valid_session (trace_len t0) p kps_idx vi st /\
    (match st with | PKeySession _ _ -> True | _ -> False))) =
  let now = global_timestamp () in
  let (|kps_vi,ser_kps_sess|) = get_session #ylm_preds #now p kps_idx in

  match parse_session_st ser_kps_sess with
  | Success (PKeySession srv k_ps) -> (|kps_vi, PKeySession srv k_ps|)
  | _ -> error "[get_lt_key_session] not a principal long term key session"

let initiator_send_msg_1 a kas_idx b =
  // get initiator long term key
  let (|_,(PKeySession srv k_as)|) = get_lt_key_session a kas_idx in

  // generate initiator nonce
  let (|_,n_a|) = rand_gen #ylm_preds public (nonce_usage "YLM.nonce_a") in

  // trigger event 'initiate'
  let event = event_initiate a b srv n_a in
  trigger_event #ylm_preds a event;

  // create and send first message
  let now = global_timestamp () in
  let msg1 = Msg1 a n_a in
  let ser_msg1 = serialize_msg now msg1 in

  let msg1_idx = send #ylm_preds #now a b ser_msg1 in

  // store initiator session
  let new_sess_idx = new_session_number #ylm_preds a in
  let st_i_sent_m1 = InitiatorSentMsg1 b n_a in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now a new_sess_idx 0 st_i_sent_m1 in

  new_session #ylm_preds #now a new_sess_idx 0 ser_st;

  (msg1_idx, new_sess_idx)

let responder_send_msg_2 b kbs_idx msg1_idx =
  // receive and parse first message
  let (|_,a,ser_msg1|) = receive_i #ylm_preds msg1_idx b in

  match parse_msg ser_msg1 with
  | Success (Msg1 a' n_a) -> (
    if a = a' then
      // get responder long term key
      let (|_,(PKeySession srv k_bs)|) = get_lt_key_session b kbs_idx in

      // generate responder nonce
      let (|_,n_b|) = rand_gen #ylm_preds (readers [P b; P a; P srv]) (nonce_usage "YLM.nonce_b") in

      // trigger event 'req key'
      let event = event_req_key a b srv n_a n_b in
      trigger_event #ylm_preds b event;

      // create and send second message
      let ev2 = EncMsg2 a n_a n_b in
      let now = global_timestamp () in
      let ser_ev2 = serialize_encval now ev2 (get_label ylm_key_usages k_bs) in
      let iv = string_to_bytes #ylm_global_usage #now "iv" in
      let ad = string_to_bytes #ylm_global_usage #now "ev2" in
      parse_serialize_encval_lemma now ev2 (get_label ylm_key_usages k_bs);
      let c_ev2 = aead_enc #ylm_global_usage #now #(get_label ylm_key_usages k_bs) k_bs iv ser_ev2 ad in

      let msg2 = Msg2 b c_ev2 in
      let ser_msg2 = serialize_msg now msg2 in

      let msg2_idx = send #ylm_preds #now b srv ser_msg2 in

      // store responder session
      let new_sess_idx = new_session_number #ylm_preds b in
      let st_r_sent_m2 = ResponderSentMsg2 a srv n_b in
      let now = global_timestamp () in
      let ser_st = serialize_session_st now b new_sess_idx 0 st_r_sent_m2 in

      new_session #ylm_preds #now b new_sess_idx 0 ser_st;

      (msg2_idx, new_sess_idx)
    else error "[r_send_m2] actual initiator does not match with initiator in first message"
  )
  | _ -> error "[r_send_m2] wrong message"

let find_auth_server_session (srv:principal) (p:principal) :
  LCrypto (si:nat & vi:nat & st:session_st) (pki ylm_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 (|si,vi,st|) t1 -> trace_len t1 == trace_len t0 /\
    valid_session (trace_len t0) srv si vi st /\
    (match st with | AuthServerSession p' _ -> p = p' | _ -> False))) =
  let now = global_timestamp () in
  let filter = (fun si vi ser_st ->
    match parse_session_st ser_st with
    | Success (AuthServerSession p' _) -> p = p' | _ -> false) in

  match find_session #ylm_preds #now srv filter with
  | Some (|si,vi,ser_st|) ->
    let Success st = parse_session_st ser_st in
    (|si,vi,st|)
  | None -> error ("[find_auth_server_session] no auth server session for " ^ p ^ " found")

#push-options "--z3rlimit 100"
let server_send_msg_3 srv msg2_idx =
  // receive and parse second message
  let (|now,b,ser_msg2|) = receive_i #ylm_preds msg2_idx srv in

  match parse_msg ser_msg2 with
  | Success (Msg2 b' c_ev_b) -> (
    if b = b' then
      // look up long term key with responder
      let (|_,_,(AuthServerSession _ k_bs)|) = find_auth_server_session srv b in

      // decrypt part of second message encrypted by responder
      let iv = string_to_bytes #ylm_global_usage #now "iv" in
      let ad = string_to_bytes #ylm_global_usage #now "ev2" in
      match aead_dec #ylm_global_usage #now #(get_label ylm_key_usages k_bs) k_bs iv c_ev_b ad with
      | Success ser_ev_b -> (
        match parse_encval ser_ev_b with
        | Success (EncMsg2 a n_a n_b) -> (
          // look up long term key with initiator
          let (|_,_,(AuthServerSession _ k_as)|) = find_auth_server_session srv a in

          // generate communication key for initiator and responder
          let (|_,k_ab|) = rand_gen #ylm_preds (readers [P srv; P a; P b]) (aead_usage "YLM.comm_key") in

          // trigger event 'send key'
          let prev = now in
          let event = event_send_key a b srv n_a n_b k_ab in
          trigger_event #ylm_preds srv event;

          // create and send third message
          let ev3_i = EncMsg3_I b k_ab n_a n_b in
          let now = global_timestamp () in
          assert(is_publishable ylm_global_usage prev k_bs \/ aead_pred ylm_usage_preds prev "YLM.lt_key" k_bs ser_ev_b ad);
          aead_dec_plaintext_publishable_if_key_and_ciphertext_publishable_forall ylm_global_usage;
          assert(is_publishable ylm_global_usage prev ser_ev_b \/ aead_pred ylm_usage_preds prev "YLM.lt_key" k_bs ser_ev_b ad);
          splittable_term_publishable_implies_components_publishable_forall ylm_global_usage;
          assert(is_publishable ylm_global_usage prev n_a /\ is_publishable ylm_global_usage prev n_b
            \/ aead_pred ylm_usage_preds prev "YLM.lt_key" k_bs ser_ev_b ad);
          readers_is_injective_2 b srv;
          assert(is_publishable ylm_global_usage prev n_a /\ is_publishable ylm_global_usage prev n_b
            \/ did_event_occur_before prev b (event_req_key a b srv n_a n_b));
          assert(is_publishable ylm_global_usage prev n_a /\ is_publishable ylm_global_usage prev n_b
            \/ (exists i. i < prev /\ is_msg ylm_global_usage i n_a public
            /\ was_rand_generated_before i n_b (readers [P b; P a; P srv]) (nonce_usage "YLM.nonce_b")));
          can_flow_later_forall cpred (get_label ylm_key_usages n_a) public;
          rand_is_secret #ylm_global_usage #now #(readers [P b; P a; P srv]) #(nonce_usage "YLM.nonce_b") n_b;
          assert(is_publishable ylm_global_usage now n_a /\ is_publishable ylm_global_usage now n_b
            \/ (exists i. later_than now i /\ is_valid ylm_global_usage i n_a /\ can_flow i (get_label ylm_key_usages n_a) public)
            /\ is_secret ylm_global_usage now n_b (readers [P b; P a; P srv]) (nonce_usage "YLM.nonce_b"));
          assert(is_msg ylm_global_usage now n_a public /\ is_publishable ylm_global_usage now n_b \/ is_secret ylm_global_usage now n_b (readers [P b; P a; P srv]) (nonce_usage "YLM.nonce_b"));
          flows_to_public_can_flow now (get_label ylm_key_usages n_a) (get_label ylm_key_usages k_as);
          flows_to_public_can_flow now (get_label ylm_key_usages n_b) (get_label ylm_key_usages k_as);
          includes_can_flow_lemma now [P b; P a; P srv] [P a; P srv];
          assert(is_msg ylm_global_usage now n_a (get_label ylm_key_usages k_as));
          assert(is_msg ylm_global_usage now n_b (get_label ylm_key_usages k_as));
          let ser_ev3_i = serialize_encval now ev3_i (get_label ylm_key_usages k_as) in
          let ad = string_to_bytes #ylm_global_usage #now "ev3_i" in
          parse_serialize_encval_lemma now ev3_i (get_label ylm_key_usages k_as);
          let c_ev3_i = aead_enc #ylm_global_usage #now #(get_label ylm_key_usages k_as) k_as iv ser_ev3_i ad in

          let ev3_r = EncMsg3_R a k_ab in
          includes_can_flow_lemma now [P srv; P a; P b] [P b; P srv];
          let ser_ev3_r = serialize_encval now ev3_r (get_label ylm_key_usages k_bs) in
          let ad = string_to_bytes #ylm_global_usage #now "ev3_r" in
          parse_serialize_encval_lemma now ev3_r (get_label ylm_key_usages k_bs);
          let c_ev3_r = aead_enc #ylm_global_usage #now #(get_label ylm_key_usages k_bs) k_bs iv ser_ev3_r ad in

          let msg3 = Msg3 c_ev3_i c_ev3_r in
          let ser_msg3 = serialize_msg now msg3 in

          let msg3_idx = send #ylm_preds #now srv a ser_msg3 in

          // store server session
          let new_sess_idx = new_session_number #ylm_preds srv in
          let st_srv_sent_m3 = AuthServerSentMsg3 a b k_ab in
          let now = global_timestamp () in
          let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sent_m3 in

          new_session #ylm_preds #now srv new_sess_idx 0 ser_st;

          (msg3_idx, new_sess_idx)
        )
        | _ -> error "[srv_send_m3] wrong responder encval"
      )
      | Error e -> error ("[srv_send_m3] " ^ e)
    else error "[srv_send_m3] actual responder does not match with responder in second message"
  )
  | _ -> error "[srv_send_m3] wrong message"
#pop-options
