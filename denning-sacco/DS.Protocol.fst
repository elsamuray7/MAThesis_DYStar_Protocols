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

#push-options "--z3rlimit 200"
let trigger_event_send_key (prev:timestamp) (a b srv:principal) (pk_a pk_b ck:bytes) (t:timestamp) (clock_cnt:nat) (cert_a cert_b:msg ds_global_usage prev public) (verk_srv:verify_key ds_global_usage prev (readers [P srv]) "DS.sig_key") :
  LCrypto timestamp (pki ds_preds)
  (requires (fun t0 -> prev < trace_len t0 /\
    (clock_cnt <= recv_msg_2_delay) /\
    parse_sigval_ cert_a == Success (CertA a pk_a t) /\
    parse_sigval_ cert_b == Success (CertB b pk_b t) /\
    (can_flow prev (readers [P srv]) public \/
      sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_a /\
      sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_b) /\
      was_rand_generated_before (trace_len t0) ck (join (readers [P a]) (get_sk_label ds_key_usages pk_b)) (aead_usage "DS.comm_key")
  ))
  (ensures (fun t0 now t1 -> now == trace_len t0 /\ trace_len t1 == trace_len t0 + 1 /\
    did_event_occur_at now a (event_send_key a b srv pk_a pk_b ck t clock_cnt))) =
  let now = global_timestamp () in
  let event = event_send_key a b srv pk_a pk_b ck t clock_cnt in
  publishable_readers_implies_corruption #prev [P srv];
  assert(corrupt_id prev (P srv) \/ sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_a);
  assert(corrupt_id prev (P srv) \/ sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_b);
  readers_is_injective srv;
  verification_key_label_lemma ds_global_usage prev verk_srv (readers [P srv]);
  assert(get_signkey_label ds_key_usages verk_srv == readers [P srv]);
  assert(corrupt_id prev (P srv)
    \/ did_event_occur_at t srv (event_certify a b srv pk_a pk_b t 0));
  trigger_event #ds_preds a event;
  now

let initiator_send_msg_3_helper (now:timestamp) (a b srv:principal) (ck pk_a pk_b:bytes) (t:timestamp) (cert_a sig_cert_a cert_b sig_cert_b:msg ds_global_usage now public) (sigk_a:sign_key ds_global_usage now (readers [P a]) "DS.sig_key") (n_sig n_pke:bytes) (clock_cnt:nat) (c_rm2:clock) :
  LCrypto (si:timestamp & c_out:clock) (pki ds_preds)
  (requires (fun t0 -> now == trace_len t0 /\
    clock_cnt == (clock_get c_rm2) /\ clock_cnt <= recv_msg_2_delay /\
    was_rand_generated_before now ck (join (readers [P a]) (get_sk_label ds_key_usages pk_b)) (aead_usage "DS.comm_key") /\
    is_msg ds_global_usage now pk_b public /\
    did_event_occur_before now a (event_send_key a b srv pk_a pk_b ck t clock_cnt) /\
    is_labeled ds_global_usage now n_sig (readers [P a]) /\
    is_pke_nonce ds_global_usage now n_pke (readers [P a])
  ))
  (ensures (fun t0 (|si,c_out|) t1 ->
     si == trace_len t0 /\
     trace_len t1 = trace_len t0 + 1 /\
     clock_get c_out = clock_cnt + 1)) =
  let l_ck = join (readers [P a]) (get_sk_label ds_key_usages pk_b) in

  // create and sign sigval containing communication key
  let sv_comm_key = CommKey ck t in
  assert(was_rand_generated_before now ck l_ck (aead_usage "DS.comm_key"));
  rand_is_secret #ds_global_usage #now #l_ck #(aead_usage "DS.comm_key") ck;
  assert(is_msg ds_global_usage now ck l_ck);
  let ser_comm_key = serialize_sigval now sv_comm_key l_ck in
  readers_is_injective a;
  assert(get_signkey_label ds_key_usages (vk #ds_global_usage #now #(readers [P a]) sigk_a) == readers [P a]);
  assert(was_rand_generated_before now ck l_ck (aead_usage "DS.comm_key"));
  assert(did_event_occur_before now a (event_send_key a b srv pk_a pk_b ck t (clock_get c_rm2)));
  parse_serialize_sigval_lemma now sv_comm_key l_ck;
  assert(can_sign now "DS.sig_key" (vk #ds_global_usage #now #(readers [P a]) sigk_a) ser_comm_key);
  let sig_comm_key = sign #ds_global_usage #now #(readers [P a]) #l_ck sigk_a n_sig ser_comm_key in

  // create and encrypt encval containing signed sigval with communication key
  let ev_comm_key = encval_comm_key ser_comm_key sig_comm_key in
  assert(is_msg ds_global_usage now ck (get_sk_label ds_key_usages pk_b));
  assert(can_flow now (get_label ds_key_usages ev_comm_key) (readers [P a]));
  let c_comm_key = pke_enc #ds_global_usage #now #(readers [P a]) pk_b n_pke ev_comm_key in

  // create and send third message
  let msg3 = Msg3 cert_a sig_cert_a cert_b sig_cert_b c_comm_key in
  let ser_msg3 = serialize_msg now msg3 in

  SR.send #now c_rm2 a b ser_msg3

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
        if verify #ds_global_usage #now #public #public verk_srv cert_a sig_cert_a then (
          if verify #ds_global_usage #now #public #public verk_srv cert_b sig_cert_b then (
            // parse certificates
            match (parse_sigval cert_a, parse_sigval cert_b) with
            | (Success (CertA a pk_a t), Success (CertB b pk_b t')) -> (
              if t <> t' then error "[i_send_m3] timestamps in initiator and responder certificates do not match"
              else
                match clock_lte t recv_msg_2_delay c_rm2 with
                | Success true -> (
                  // validate public key of initiator
                  let pk_a' = get_public_key #ds_preds #now a a PKE "DS.pke_key" in
                  if pk_a <> pk_a' then error "[i_send_m3] wrong initiator public key"
                  else
                    // generate communication key
                    let prev = now in
                    let l_ck = join (readers [P a]) (get_sk_label ds_key_usages pk_b) in
                    let (|_,ck|) = rand_gen #ds_preds l_ck (aead_usage "DS.comm_key") in

                    // trigger event 'send_key'
                    parse_sigval_lemma cert_a;
                    parse_sigval_lemma cert_b;
                    let clock_cnt_event = clock_get c_rm2 in
                    let t_event = trigger_event_send_key prev a b srv pk_a pk_b ck t clock_cnt_event cert_a cert_b verk_srv in

                    // look up sign key of initiator and generate sign nonce
                    let now = global_timestamp () in
                    let (|_,sigk_a|) = get_private_key #ds_preds #now a SIG "DS.sig_key" in
                    let (|_,n_sig|) = rand_gen #ds_preds (readers [P a]) (nonce_usage "SIG_NONCE") in

                    // generate pke nonce
                    let (|_,n_pke|) = rand_gen #ds_preds (readers [P a]) (nonce_usage "PKE_NONCE") in

                    // create and send third message
                    let now = global_timestamp () in
                    let cert_a:msg ds_global_usage now public = cert_a in
                    let sig_cert_a:msg ds_global_usage now public = sig_cert_a in
                    let cert_b:msg ds_global_usage now public = cert_b in
                    let sig_cert_b:msg ds_global_usage now public = sig_cert_b in
                    let (|msg3_idx,c_out|) = initiator_send_msg_3_helper now a b srv ck pk_a pk_b t cert_a sig_cert_a cert_b sig_cert_b sigk_a n_sig n_pke clock_cnt_event c_rm2 in

                    // update initiator session
                    let st_i_sent_m3 = InitiatorSentMsg3 b srv ck in
                    let now = global_timestamp () in
                    assert(corrupt_id prev (P srv) \/ is_pub_enc_key t pk_b b);
                    sk_label_lemma ds_global_usage t pk_b (readers [P b]);
                    let ser_st = serialize_session_st now a a_si a_vi st_i_sent_m3 in

                    update_session #ds_preds #now a a_si a_vi ser_st;

                    (msg3_idx, c_out)
                )
                | Success false -> error "[i_send_m3] message has been replayed"
                | Error e -> error e
            )
            | _ -> error "[i_send_m3] wrong sigvals"
          ) else error "[i_send_m3] verification of responder certificate failed"
        ) else error "[i_send_m3] verification of initiator certificate failed"
      )
      | _ -> error "[i_send_m3] wrong message"
  )
  | _ -> error "[i_send_m3] wrong session"
#pop-options
