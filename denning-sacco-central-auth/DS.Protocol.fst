module DS.Protocol


let initiator_send_msg_1 a b =
  // trigger event 'initiate'
  let event = event_initiate a b in
  trigger_event #ds_preds a event;

  // create and send first message
  let now = global_timestamp () in
  let msg1:message now = Msg1 a b in
  let ser_msg1 = serialize_msg now msg1 in

  let msg1_idx = send #ds_preds #now a auth_srv ser_msg1 in

  // create and store initiator session
  let new_sess_idx = new_session_number #ds_preds a in
  let st_i_sent_m1 = InitiatorSentMsg1 b in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now a new_sess_idx 0 st_i_sent_m1 in

  new_session #ds_preds #now a new_sess_idx 0 ser_st;

  (msg1_idx, new_sess_idx)

#push-options "--z3rlimit 50"
let server_send_msg_2 msg1_idx =
  // receive and parse first message
  let (|now,a,ser_msg1|) = receive_i #ds_preds msg1_idx auth_srv in

  match parse_msg ser_msg1 with
  | Success (Msg1 a' b) -> (
    if a <> a' then error "[srv_send_m2] initiator from received message does not match with actual initiator"
    else
      // look up public keys of initiator and responder
      let pk_a = get_public_key #ds_preds #now auth_srv a SIG "DS.sig_key" in
      let pk_b = get_public_key #ds_preds #now auth_srv b PKE "DS.pke_key" in

      // initialize clock
      let t = global_timestamp () in
      let c_new = clock_new () in

      // trigger event 'certify'
      let event = event_certify a b pk_a pk_b t (clock_get c_new) in
      trigger_event #ds_preds auth_srv event;

      // look up sign key of server and generate sign nonce
      let now = global_timestamp () in
      let (|_,sigk_srv|) = get_private_key #ds_preds #now auth_srv SIG "DS.sig_key" in
      let (|_,n_sig|) = rand_gen #ds_preds (readers [P auth_srv]) (nonce_usage "SIG_NONCE") in

      // create and sign initiator certificate
      let cert_a = CertA a pk_a t in
      let now = global_timestamp () in
      let ser_cert_a = serialize_sigval now cert_a public in
      readers_is_injective auth_srv;
      assert(get_signkey_label ds_key_usages (vk #ds_global_usage #now #(readers [P auth_srv]) sigk_srv) == readers [P auth_srv]);
      assert(did_event_occur_before now auth_srv (event_certify a b pk_a pk_b t 0));
      parse_serialize_sigval_lemma now cert_a public;
      assert(can_sign now "DS.sig_key" (vk #ds_global_usage #now #(readers [P auth_srv]) sigk_srv) ser_cert_a);
      let sig_cert_a = sign #ds_global_usage #now #(readers [P auth_srv]) #public sigk_srv n_sig ser_cert_a in

      // create and sign responder certificate
      let cert_b = CertB b pk_b t in
      let ser_cert_b = serialize_sigval now cert_b public in
      parse_serialize_sigval_lemma now cert_b public;
      assert(can_sign now "DS.sig_key" (vk #ds_global_usage #now #(readers [P auth_srv]) sigk_srv) ser_cert_b);
      let sig_cert_b = sign #ds_global_usage #now #(readers [P auth_srv]) #public sigk_srv n_sig ser_cert_b in

      // create and send second message
      let msg2 = Msg2 ser_cert_a sig_cert_a ser_cert_b sig_cert_b in
      let ser_msg2 = serialize_msg now msg2 in

      let (|msg2_idx,c_out|) = SR.send #now c_new auth_srv a ser_msg2 in

      // create and store server session
      let new_sess_idx = new_session_number #ds_preds auth_srv in
      let st_srv_sent_m2 = AuthServerSentMsg2 a b in
      let now = global_timestamp () in
      let ser_st = serialize_session_st now auth_srv new_sess_idx 0 st_srv_sent_m2 in

      new_session #ds_preds #now auth_srv new_sess_idx 0 ser_st;

      (msg2_idx, new_sess_idx, c_out)
  )
  | _ -> error "[srv_send_m2] wrong message"
#pop-options

#push-options "--z3rlimit 200"
let trigger_event_send_key (prev:timestamp) (a b:principal) (pk_a pk_b ck:bytes) (t:timestamp) (clock_cnt:nat) (cert_a cert_b:msg ds_global_usage prev public) (verk_srv:verify_key ds_global_usage prev (readers [P auth_srv]) "DS.sig_key") :
  LCrypto timestamp (pki ds_preds)
  (requires (fun t0 -> prev < trace_len t0 /\
    clock_cnt <= recv_msg_2_delay /\
    was_rand_generated_before (trace_len t0) ck (join (readers [P a]) (get_sk_label ds_key_usages pk_b)) (aead_usage "DS.comm_key") /\
    parse_sigval_ cert_a == Success (CertA a pk_a t) /\
    parse_sigval_ cert_b == Success (CertB b pk_b t) /\
    (can_flow prev (readers [P auth_srv]) public \/
    sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_a /\
    sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_b)
  ))
  (ensures (fun t0 now t1 -> now == trace_len t0 /\ trace_len t1 == trace_len t0 + 1 /\
    did_event_occur_at now a (event_send_key a b pk_a pk_b ck t clock_cnt))) =
  let now = global_timestamp () in
  let event = event_send_key a b pk_a pk_b ck t clock_cnt in
  publishable_readers_implies_corruption #prev [P auth_srv];
  assert(corrupt_id prev (P auth_srv) \/ sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_a);
  assert(corrupt_id prev (P auth_srv) \/ sign_pred ds_usage_preds prev "DS.sig_key" verk_srv cert_b);
  readers_is_injective auth_srv;
  verification_key_label_lemma ds_global_usage prev verk_srv (readers [P auth_srv]);
  assert(get_signkey_label ds_key_usages verk_srv == readers [P auth_srv]);
  assert(corrupt_id prev (P auth_srv)
    \/ did_event_occur_at t auth_srv (event_certify a b pk_a pk_b t 0));
  sk_label_lemma ds_global_usage t pk_b (readers [P b]);
  trigger_event #ds_preds a event;
  now

let initiator_send_msg_3_helper (now:timestamp) (a b:principal) (ck pk_a pk_b:bytes) (t:timestamp) (cert_a sig_cert_a cert_b sig_cert_b:msg ds_global_usage now public) (sigk_a:sign_key ds_global_usage now (readers [P a]) "DS.sig_key") (n_sig n_pke:bytes) (clock_cnt:nat) (c_rm2:clock) :
  LCrypto (si:timestamp & c_out:clock) (pki ds_preds)
  (requires (fun t0 -> now == trace_len t0 /\ now > 2 /\
    clock_cnt == (clock_get c_rm2) /\ clock_cnt <= recv_msg_2_delay /\
    was_rand_generated_before now ck (join (readers [P a]) (get_sk_label ds_key_usages pk_b)) (aead_usage "DS.comm_key") /\
    is_ver_key now pk_a a /\ pk_a == vk #ds_global_usage #now #(readers [P a]) sigk_a /\
    is_msg ds_global_usage now pk_b public /\
    did_event_occur_at (now-3) a (event_send_key a b pk_a pk_b ck t clock_cnt) /\
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
  verification_key_label_lemma ds_global_usage now pk_a (readers [P a]);
  assert(get_signkey_label ds_key_usages pk_a == readers [P a]);
  assert(was_rand_generated_before now ck l_ck (aead_usage "DS.comm_key"));
  assert(did_event_occur_before now a (event_send_key a b pk_a pk_b ck t (clock_get c_rm2)));
  parse_serialize_sigval_lemma now sv_comm_key l_ck;
  assert(can_sign now "DS.sig_key" pk_a ser_comm_key);
  let sig_comm_key = sign #ds_global_usage #now #(readers [P a]) #l_ck sigk_a n_sig ser_comm_key in

  // create and encrypt encval containing signed sigval with communication key
  let ev_comm_key = encval_comm_key now ser_comm_key sig_comm_key l_ck in
  assert(is_msg ds_global_usage now ck (get_sk_label ds_key_usages pk_b));
  assert(can_flow now (get_label ds_key_usages ev_comm_key) (readers [P a]));
  parse_serialize_encval_lemma #now #l_ck ser_comm_key sig_comm_key;
  assert(can_pke_encrypt now "DS.pke_key" pk_b ev_comm_key);
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
  | Success (InitiatorSentMsg1 b) -> (
    // receive and parse second message
    let (|now,c_rm2,auth_srv',ser_msg2|) = SR.receive_i msg2_idx c_in a in

    if auth_srv <> auth_srv' then error "[i_send_m3] sender of second message is not auth server"
    else
      match parse_msg ser_msg2 with
      | Success (Msg2 cert_a sig_cert_a cert_b sig_cert_b) -> (
        // look up verification key of server
        let verk_srv = get_public_key #ds_preds #now a auth_srv SIG "DS.sig_key" in

        // verify initiator and responder certificates
        if verify #ds_global_usage #now #public #public verk_srv cert_a sig_cert_a then (
          if verify #ds_global_usage #now #public #public verk_srv cert_b sig_cert_b then (
            // parse certificates
            match (parse_sigval cert_a, parse_sigval cert_b) with
            | (Success (CertA a' pk_a t), Success (CertB b' pk_b t')) -> (
              if a <> a' || b <> b' then error "[i_send_m3] initiator or responder from certificate does not match with actual initiator or responder"
              else if t <> t' then error "[i_send_m3] timestamps in initiator and responder certificates do not match"
              else
                // check whether message is replay
                match clock_lte t recv_msg_2_delay c_rm2 with
                | Success true -> (
                  // look up sign key of initiator
                  let (|_,sigk_a|) = get_private_key #ds_preds #now a SIG "DS.sig_key" in

                  // validate public key of initiator
                  let verk_a = vk #ds_global_usage #now #(readers [P a]) sigk_a in
                  if pk_a <> verk_a then error "[i_send_m3] wrong initiator public key"
                  else
                    // generate communication key
                    let prev = now in
                    let l_ck = join (readers [P a]) (get_sk_label ds_key_usages pk_b) in
                    let (|_,ck|) = rand_gen #ds_preds l_ck (aead_usage "DS.comm_key") in

                    // trigger event 'send_key'
                    parse_sigval_lemma cert_a;
                    parse_sigval_lemma cert_b;
                    let clock_cnt_event = clock_get c_rm2 in
                    let t_event = trigger_event_send_key prev a b pk_a pk_b ck t clock_cnt_event cert_a cert_b verk_srv in

                    // generate sign and pke nonce
                    let (|_,n_sig|) = rand_gen #ds_preds (readers [P a]) (nonce_usage "SIG_NONCE") in
                    let (|_,n_pke|) = rand_gen #ds_preds (readers [P a]) (nonce_usage "PKE_NONCE") in

                    // create and send third message
                    let now = global_timestamp () in
                    let cert_a:msg ds_global_usage now public = cert_a in
                    let sig_cert_a:msg ds_global_usage now public = sig_cert_a in
                    let cert_b:msg ds_global_usage now public = cert_b in
                    let sig_cert_b:msg ds_global_usage now public = sig_cert_b in
                    let (|msg3_idx,c_out|) = initiator_send_msg_3_helper now a b ck pk_a pk_b t cert_a sig_cert_a cert_b sig_cert_b sigk_a n_sig n_pke clock_cnt_event c_rm2 in

                    // update initiator session
                    let st_i_sent_m3 = InitiatorSentMsg3 b ck in
                    let now = global_timestamp () in
                    assert(corrupt_id prev (P auth_srv) \/ is_pub_enc_key t pk_b b);
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

#push-options "--z3rlimit 400"
let trigger_event_accept_key (now:timestamp) (a b:principal) (pk_a pk_b ck:bytes)
  (t:timestamp) (clock_cnt:nat) (cert_a cert_b:msg ds_global_usage now public)
  (ev_comm_key:msg ds_global_usage now (readers [P b]))
  (ser_comm_key:msg ds_global_usage now (readers [P b]))
  (verk_srv:verify_key ds_global_usage now (readers [P auth_srv]) "DS.sig_key") :
  LCrypto unit (pki ds_preds)
  (requires (fun t0 -> now == trace_len t0 /\
    clock_cnt <= recv_msg_3_delay /\
    a =!= b /\
    is_pub_enc_key now pk_b b /\
    parse_sigval_ cert_a == Success (CertA a pk_a t) /\
    parse_sigval_ cert_b == Success (CertB b pk_b t) /\
    parse_sigval_ ser_comm_key == Success (CommKey ck t) /\
    (exists sig_ck. parse_encval_comm_key_ ev_comm_key == Success (ser_comm_key, sig_ck)) /\
    (can_flow now (readers [P auth_srv]) public \/
    sign_pred ds_usage_preds now "DS.sig_key" verk_srv cert_a /\
    sign_pred ds_usage_preds now "DS.sig_key" verk_srv cert_b) /\
    (is_ver_key now pk_a a ==> (can_flow now (readers [P a]) public \/
    sign_pred ds_usage_preds now "DS.sig_key" pk_a ser_comm_key))
  ))
  (ensures (fun t0 _ t1 -> trace_len t1 == trace_len t0 + 1 /\
    did_event_occur_at now b (event_accept_key a b pk_a pk_b ck t clock_cnt) /\
    (corrupt_id now (P auth_srv) \/ corrupt_id now (P a) \/
    was_rand_generated_before now ck (join (readers [P a]) (readers [P b])) (aead_usage "DS.comm_key")))) =
  let event = event_accept_key a b pk_a pk_b ck t clock_cnt in

  // publishable server id means that server is corrupted
  publishable_readers_implies_corruption #now [P auth_srv];
  assert(corrupt_id now (P auth_srv) \/ sign_pred ds_usage_preds now "DS.sig_key" verk_srv cert_a);
  assert(corrupt_id now (P auth_srv) \/ sign_pred ds_usage_preds now "DS.sig_key" verk_srv cert_b);

  // use readers injectivity to infer that server triggered certify event (if honest)
  readers_is_injective auth_srv;
  verification_key_label_lemma ds_global_usage now verk_srv (readers [P auth_srv]);
  assert(get_signkey_label ds_key_usages verk_srv == readers [P auth_srv]);
  assert(corrupt_id now (P auth_srv) \/ t < now /\ did_event_occur_at t auth_srv (event_certify a b pk_a pk_b t 0));

  // certify event pred ensures that pk_a is initiator's verify key (if server is honest)
  assert(corrupt_id now (P auth_srv) \/ epred t auth_srv (event_certify a b pk_a pk_b t 0));
  assert(corrupt_id now (P auth_srv) \/ t < now);
  assert(corrupt_id now (P auth_srv) \/ is_ver_key t pk_a a);
  verification_key_label_lemma ds_global_usage t pk_a (readers [P a]);
  assert(corrupt_id now (P auth_srv) \/ get_signkey_label ds_key_usages pk_a == readers [P a]);
  is_verify_key_later t pk_a;
  assert(corrupt_id now (P auth_srv) \/ is_ver_key now pk_a a);
  assert(corrupt_id now (P auth_srv) \/ can_flow now (readers [P a]) public
    \/ sign_pred ds_usage_preds now "DS.sig_key" pk_a ser_comm_key);

  // publishable initiator id means that initiator is corrupted
  publishable_readers_implies_corruption #now [P a];
  assert(corrupt_id now (P auth_srv) \/ corrupt_id now (P a)
    \/ sign_pred ds_usage_preds now "DS.sig_key" pk_a ser_comm_key);

  // use readers injectivity to infer that initiator triggered send key event (if initiator and server are honest)
  readers_is_injective a;
  assert(corrupt_id now (P auth_srv) \/ corrupt_id now (P a)
    \/ (exists i. later_than now i /\ can_sign i "DS.sig_key" pk_a ser_comm_key));
  assert(corrupt_id now (P auth_srv) \/ corrupt_id now (P a)
    \/ (exists i. later_than now i /\ (i > 2 /\
    (exists b' pk_b'. was_rand_generated_before i ck (join (readers [P a]) (get_sk_label ds_key_usages pk_b')) (aead_usage "DS.comm_key") /\
    (exists clock_cnt'. clock_cnt' <= recv_msg_2_delay /\ did_event_occur_at (i-3) a (event_send_key a b' pk_a pk_b' ck t clock_cnt'))))));

  trigger_event #ds_preds b event

let responder_recv_msg_3 c_in b msg3_idx =
  // receive and parse second message
  let (|_,c_out,a,ser_msg3|) = SR.receive_i msg3_idx c_in b in

  match parse_msg ser_msg3 with
  | Success (Msg3 cert_a sig_cert_a cert_b sig_cert_b c_comm_key) -> (
    // look up verification key of server
    let now = global_timestamp () in
    let verk_srv = get_public_key #ds_preds #now b auth_srv SIG "DS.sig_key" in

    // verify initiator and responder certificates
    if verify #ds_global_usage #now #public #public verk_srv cert_a sig_cert_a then (
      if verify #ds_global_usage #now #public #public verk_srv cert_b sig_cert_b then (
        // parse certificates
        match (parse_sigval cert_a, parse_sigval cert_b) with
        | (Success (CertA a' pk_a t), Success (CertB b' pk_b t')) -> (
          if a <> a' || b <> b' then error "[r_recv_m3] initiator or responder from certificate does not match with actual initiator or responder"
          // This is a reasonable assumption required to show key secrecy, otherwise no key exchange would be necessary
          else if a = b then error "[r_recv_m3] initiator and responder are the same principal"
          else if t <> t' then error "[r_recv_m3] timestamps in initiator and responder certificates do not match"
          else
            // look up private key of responder
            let (|_,sk_b|) = get_private_key #ds_preds #now b PKE "DS.pke_key" in

            // validate public key of responder
            let pk_b' = pk #ds_global_usage #now #(readers [P b]) sk_b in
            if pk_b <> pk_b' then error "[r_recv_m3] wrong responder public key"
            else
              // decrypt communication key and timestamp encrypted and signed by initiator
              match pke_dec #ds_global_usage #now #(readers [P b]) sk_b c_comm_key with
              | Success ev_comm_key -> (
                // parse encval containing communication key and timestamp signed by initiator
                match parse_encval_comm_key ev_comm_key with
                | Success (ser_comm_key, sig_comm_key) -> (
                  // verify signed communication key and timestamp
                  if verify #ds_global_usage #now #(readers [P b]) #(readers [P b]) pk_a ser_comm_key sig_comm_key then (
                    // parse signed communication key and timestamp
                    match parse_sigval #now #(readers [P b]) ser_comm_key with
                    | Success (CommKey ck t'') -> (
                      if t <> t'' then error "[r_recv_m3] wrong timestamp in sigval"
                      else
                        // check whether message is replay
                        match clock_lte t recv_msg_3_delay c_out with
                        | Success true -> (
                          // trigger event 'accept key'
                          parse_sigval_lemma cert_a;
                          parse_sigval_lemma cert_b;
                          parse_sigval_lemma #now #(readers [P b]) ser_comm_key;
                          parse_encval_lemma ev_comm_key;
                          let clock_cnt_event = clock_get c_out in
                          trigger_event_accept_key now a b pk_a pk_b ck t clock_cnt_event cert_a cert_b ev_comm_key ser_comm_key verk_srv;

                          // store responder session
                          let new_sess_idx = new_session_number #ds_preds b in
                          let st_r_rcvd_m3 = ResponderRecvedMsg3 a ck in
                          let now = global_timestamp () in
                          rand_is_secret #ds_global_usage #now #(join (readers [P a]) (readers [P b])) #(aead_usage "DS.comm_key") ck;
                          let ser_st = serialize_session_st now b new_sess_idx 0 st_r_rcvd_m3 in

                          new_session #ds_preds #now b new_sess_idx 0 ser_st;

                          (new_sess_idx, c_out)
                        )
                        | Success false -> error "[r_recv_m3] message has been replayed"
                        | Error e -> error e
                    )
                    | _ -> error "[r_recv_m3] wrong sigval"
                  ) else error "[r_recv_m3] verification of signed communication key and timestamp failed"
                )
                | _ -> error "[r_recv_m3] parsing encval containing communication key failed"
              )
              | Error e -> error ("[r_recv_m3] decryption of encrypted and signed communication key and timestamp failed: " ^ e)
        )
        | _ -> error "[r_recv_m3] wrong sigvals"
      ) else error "[r_recv_m3] verification of responder certificate failed"
    ) else error "[r_recv_m3] verification of initiator certificate failed"
  )
  | _ -> error "[r_recv_m3] wrong message"
#pop-options
