module DS.Protocol


(* Needs access to internal clock implementation *)
friend DS.Clock


let initiator_send_msg_1 a b srv =
  // trigger event 'initiate'
  let event = event_initiate a b srv in
  trigger_event #ds_preds a event;

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

#push-options "--z3rlimit 50"
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

      // initialize clock
      let t = global_timestamp () in
      let c_new = clock_new t in

      // trigger event 'certify'
      let event = event_certify a b srv pk_a pk_b t (clock_get c_new) in
      trigger_event #ds_preds srv event;

      // look up sign key of server and generate sign nonce
      let now = global_timestamp () in
      let (|_,sigk_srv|) = get_private_key #ds_preds #now srv SIG "DS.sig_key" in
      let (|_,n_sig|) = rand_gen #ds_preds (readers [P srv]) (nonce_usage "SIG_NONCE") in

      // create and sign initiator certificate
      let cert_a = CertA a pk_a t in
      let now = global_timestamp () in
      let ser_cert_a = serialize_sigval now cert_a public in
      readers_is_injective srv;
      assert(get_signkey_label ds_key_usages (vk #ds_global_usage #now #(readers [P srv]) sigk_srv) == readers [P srv]);
      assert(did_event_occur_before now srv (event_certify a b srv pk_a pk_b t 0));
      parse_serialize_sigval_lemma now cert_a public;
      assert(can_sign now "DS.sig_key" (vk #ds_global_usage #now #(readers [P srv]) sigk_srv) ser_cert_a);
      let sig_cert_a = sign #ds_global_usage #now #(readers [P srv]) #public sigk_srv n_sig ser_cert_a in

      // create and sign responder certificate
      let cert_b = CertB b pk_b t in
      let ser_cert_b = serialize_sigval now cert_b public in
      parse_serialize_sigval_lemma now cert_b public;
      assert(can_sign now "DS.sig_key" (vk #ds_global_usage #now #(readers [P srv]) sigk_srv) ser_cert_b);
      let sig_cert_b = sign #ds_global_usage #now #(readers [P srv]) #public sigk_srv n_sig ser_cert_b in

      // create and send second message
      let msg2 = Msg2 ser_cert_a sig_cert_a ser_cert_b sig_cert_b in
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
#pop-options

let initiator_send_msg_3 c_in a msg2_idx a_si =
  // get and parse initiator session
  let now = global_timestamp () in
  let (|a_vi,ser_st|) = get_session #ds_preds #now a a_si in

  match parse_session_st ser_st with
  | Success (InitiatorSentMsg1 b srv) -> (
    // receive and parse second message
    let (|now,c_rm2,srv',ser_msg2|) = SR.receive_i msg2_idx c_in a in

    if srv <> srv' then error "[i_send_m3] server stored in session does not match with actual server"
    else
      match parse_msg ser_msg2 with
      | Success (Msg2 cert_a sig_cert_a cert_b sig_cert_b) -> (
        // look up verification key of server
        let verk_srv = get_public_key #ds_preds #now a srv SIG "DS.sig_key" in

        // verify initiator and responder certificates
        if verify #ds_global_usage #now #public #public verk_srv cert_a sig_cert_a then
          if verify #ds_global_usage #now #public #public verk_srv cert_b sig_cert_b then
            // parse certificates
            match (parse_sigval cert_a, parse_sigval cert_b) with
            | (Success (CertA a pk_a t), Success (CertB b pk_b t')) -> (
              if t <> t' then error "[i_send_m3] timestamps in initiator and responder certificates do not match"
              else
                if clock_lte t recv_msg_2_delay c_rm2 then
                  // validate public key of initiator
                  let pk_a' = get_public_key #ds_preds #now a a PKE "DS.pke_key" in
                  if pk_a <> pk_a' then error "[i_send_m3] wrong initiator public key"
                  else
                    // generate communication key
                    let (|_,ck|) = rand_gen #ds_preds (readers [P a; P b]) (aead_usage "DS.comm_key") in

                    // look up sign key of initiator and generate sign nonce
                    let (|_,sigk_a|) = get_private_key #ds_preds #now a SIG "DS.sig_key" in
                    let (|_,n_sig|) = rand_gen #ds_preds (readers [P a]) (nonce_usage "SIG_NONCE") in

                    // generate pke nonce
                    let (|_,n_pke|) = rand_gen #ds_preds (readers [P a]) (nonce_usage "PKE_NONCE") in

                    // create and sign sigval containing communication key
                    let sv_comm_key = CommKey ck t in
                    let now = global_timestamp () in
                    let ser_comm_key = serialize_sigval now sv_comm_key (readers [P a; P b]) in
                    let sig_comm_key = sign #ds_global_usage #now #(readers [P a]) #(readers [P a; P b]) sigk_a n_sig ser_comm_key in

                    // create and encrypt encval containing signed sigval with communication key
                    let ev_comm_key = encval_comm_key ser_comm_key sig_comm_key in
                    let c_comm_key = pke_enc #ds_global_usage #now #(readers [P a]) pk_b n_pke ev_comm_key in

                    // create and send third message
                    let msg3 = Msg3 ser_cert_a sig_cert_a ser_cert_b sig_cert_b c_comm_key in
                    let ser_msg3 = serialize_msg now msg3 in

                    let (|msg3_idx,c_out|) = SR.send #now c_rm2 a b ser_msg3 in

                    // update initiator session
                    let st_i_sent_m3 = InitiatorSentMsg3 b ck in
                    let now = global_timestamp () in
                    let ser_st = serialize_session_st now a a_si a_vi st_i_sent_m3 in

                    update_session #ds_preds #now a a_si a_vi ser_st;

                    (msg3_idx, c_out)
                else error "[i_send_m3] message has been replayed"
            )
            | _ -> error "[i_send_m3] wrong sigvals"
          else error "[i_send_m3] verification of responder certificate failed"
        else error "[i_send_m3] verification of initiator certificate failed"
      )
      | _ -> error "[i_send_m3] wrong message"
  )
  | _ -> error "[i_send_m3] wrong session"
