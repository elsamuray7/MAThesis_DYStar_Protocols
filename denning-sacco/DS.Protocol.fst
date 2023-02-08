module DS.Protocol


(* Needs access to internal clock implementation *)
friend DS.Clock


let initiator_send_msg_1 a b srv =
  // create and send first message
  let now = global_timestamp () in
  let msg1:message now = Msg1 a b in
  let ser_msg1 = serialize_msg now msg1 in

  let msg1_idx = send #ds_preds #now a srv ser_msg1 in

  // create and store initiator session
  let new_sess_idx = new_session_number #ds_preds a in
  let st_i_sent_m1 = InitiatorSentMsg1 b srv in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now a new_sess_idx 0 st_i_sent_m1 in

  new_session #ds_preds #now a new_sess_idx 0 ser_st;

  (msg1_idx, new_sess_idx)

let server_send_msg_2 srv msg1_idx =
  // receive and parse first message
  let (|now,a,ser_msg1|) = receive_i #ds_preds msg1_idx srv in

  match parse_msg ser_msg1 with
  | Success (Msg1 a' b) -> (
    if a <> a' then error "[srv_send_m2] initiator from received message does not match with actual initiator"
    else
      // look up public keys of initiator and responder
      let pk_a = get_public_key #ds_preds #now srv a PKE "DS.pke_key" in
      let pk_b = get_public_key #ds_preds #now srv b PKE "DS.pke_key" in

      // look up sign key of server and generate sign nonce
      let (|_,sigk_srv|) = get_private_key #ds_preds #now srv SIG "DS.sig_key" in
      let (|_,n_sig|) = rand_gen #ds_preds (readers [P srv]) (nonce_usage "SIG_NONCE") in

      // initialize clock
      let now = global_timestamp () in
      let c_new = clock_new now in

      // create and send second message
      let esv_sig_cert_a = SigCertP a pk_a now in
      let ser_cert_a = serialize_encsigval now esv_sig_cert_a public in
      let sig_cert_a = sign #ds_global_usage #now #(readers [P srv]) #public sigk_srv n_sig ser_cert_a in

      let esv_sig_cert_b = SigCertP b pk_b now in
      let ser_cert_b = serialize_encsigval now esv_sig_cert_b public in
      let sig_cert_b = sign #ds_global_usage #now #(readers [P srv]) #public sigk_srv n_sig ser_cert_b in

      let msg2 = Msg2 sig_cert_a sig_cert_b in
      let ser_msg2 = serialize_msg now msg2 in

      let (|msg2_idx,c_out|) = SR.send #now c_new srv a ser_msg2 in

      // create and store server session
      let new_sess_idx = new_session_number #ds_preds srv in
      let st_srv_sent_m2 = AuthServerSentMsg2 a b in
      let now = global_timestamp () in
      let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sent_m2 in

      new_session #ds_preds #now srv new_sess_idx 0 ser_st;

      (msg2_idx, new_sess_idx, c_out)
  )
  | _ -> error "[srv_send_m2] wrong message"
