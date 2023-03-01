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
