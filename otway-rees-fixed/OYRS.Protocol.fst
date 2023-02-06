module OYRS.Protocol


let initiator_init a srv b =
  let (|i,k_as|) = rand_gen #oyrs_preds (readers [P a; P srv]) (aead_usage "sk_i_srv") in
  let new_sess_idx = new_session_number #oyrs_preds a in
  let st_i_init = InitiatorInit srv k_as b in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now a new_sess_idx 0 st_i_init in
  new_session #oyrs_preds #now a new_sess_idx 0 ser_st;
  ((|i,"sk_i_srv",k_as|), new_sess_idx)

let responder_init b srv =
  let (|i,k_bs|) = rand_gen #oyrs_preds (readers [P b; P srv]) (aead_usage "sk_r_srv") in
  let new_sess_idx = new_session_number #oyrs_preds b in
  let st_r_init = ResponderInit srv k_bs in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now b new_sess_idx 0 st_r_init in
  new_session #oyrs_preds #now b new_sess_idx 0 ser_st;
  ((|i,"sk_r_srv",k_bs|), new_sess_idx)

let install_sk_at_auth_server #i #us srv p sk =
  let new_sess_idx = new_session_number #oyrs_preds srv in
  let st_srv_sess = AuthServerSession p sk us in
  let now = global_timestamp () in

  // Prove that sk can flow to srv at now
  can_flow_later i now (readers [P p; P srv]) (readers [P p; P srv]);
  is_valid_later oyrs_global_usage i now sk;
  can_flow_transitive now (get_label oyrs_key_usages sk) (readers [P p; P srv]) (readers [P srv]);
  let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sess in

  new_session #oyrs_preds #now srv new_sess_idx 0 ser_st

#push-options "--z3rlimit 300"
let initiator_send_msg_1 a a_ii =
  // get initiator session
  let now = global_timestamp () in
  let (|_,ser_st|) = get_session #oyrs_preds #now a a_ii in

  match parse_session_st ser_st with
  | Success (InitiatorInit srv k_as b) -> (
    // generate conversation id and initiator nonce
    let (|_,c|) = rand_gen #oyrs_preds public (nonce_usage "conv_id") in
    let (|now,n_a|) = rand_gen #oyrs_preds (readers [P a; P srv]) (nonce_usage "nonce_i") in

    // trigger event 'initiate'
    let event = event_initiate c a b srv n_a in
    trigger_event #oyrs_preds a event;

    // create and send first message
    let ev1 = EncMsg1 c a b n_a in
    let now = global_timestamp () in
    let (|tag_ev1,ser_ev1|) = serialize_encval now ev1 (get_label oyrs_key_usages k_as) in
    assert(tag_ev1 = "ev1");
    parse_serialize_encval_lemma now ev1 (get_label oyrs_key_usages k_as);
    let c_ev1 = aead_enc #oyrs_global_usage #now #(get_label oyrs_key_usages k_as) k_as (string_to_bytes #oyrs_global_usage #now "iv") ser_ev1 (string_to_bytes #oyrs_global_usage #now "ev1") in

    let msg1:message now = Msg1 c a b (|tag_ev1,c_ev1|) in
    let ser_msg1 = serialize_msg now msg1 in

    let send_m1_idx = send #oyrs_preds a b ser_msg1 in

    // update initiator session
    let new_sess_idx = new_session_number #oyrs_preds a in
    let st_i_m1 = InitiatorSentMsg1 srv k_as b c n_a in
    let now = global_timestamp () in
    let ser_st = serialize_session_st now a new_sess_idx 0 st_i_m1 in
    new_session #oyrs_preds #now a new_sess_idx 0 ser_st;

    (new_sess_idx, send_m1_idx)
  )
  | _ -> error "i_send_m1: wrong session\n"

let responder_send_msg_2 b msg1_idx b_ii =
  // get responder session
  let now = global_timestamp () in
  let (|_,ser_st|) = get_session #oyrs_preds #now b b_ii in

  match parse_session_st ser_st with
  | Success (ResponderInit srv k_bs) -> (
    // receive and parse first message
    let (|_,a,ser_msg1|) = receive_i #oyrs_preds msg1_idx b in

    match parse_msg ser_msg1 with
    | Success (Msg1 c a' b' (|tag_ev_a,c_ev_a|)) -> (
      if b <> b' then error "r_send_m2: responder in message does not match with actual responder\n"
      // TODO: should remove check, where some principal is compared with principal returned by "receive_i" function?
      else if a <> a' then error "r_send_m2: initiator in message does not match with actual initiator\n"
      else
        // generate responder nonce
        let (|_,n_b|) = rand_gen #oyrs_preds (readers [P b; P srv]) (nonce_usage "nonce_r") in

        // trigger event 'request key'
        let event = event_request_key c a b srv n_b in
        trigger_event #oyrs_preds b event;

        // create and send second message
        let ev2 = EncMsg2 c a b n_b in
        let now = global_timestamp () in
        let (|tag_ev2,ser_ev2|) = serialize_encval now ev2 (get_label oyrs_key_usages k_bs) in
        assert(tag_ev2 = "ev2");
        parse_serialize_encval_lemma now ev2 (get_label oyrs_key_usages k_bs);
        let c_ev2 = aead_enc #oyrs_global_usage #now #(get_label oyrs_key_usages k_bs) k_bs (string_to_bytes #oyrs_global_usage #now "iv") ser_ev2 (string_to_bytes #oyrs_global_usage #now "ev2") in

        let c_ev_a:msg oyrs_global_usage now public = c_ev_a in
        let msg2:message now = Msg2 c a b (|tag_ev_a,c_ev_a|) (|tag_ev2,c_ev2|) in
        let ser_msg2 = serialize_msg now msg2 in

        let send_m2_idx = send #oyrs_preds b srv ser_msg2 in

        // update responder session
        let new_sess_idx = new_session_number #oyrs_preds b in
        let st_r_m2 = ResponderSentMsg2 srv k_bs a c n_b in
        let now = global_timestamp () in
        let ser_st = serialize_session_st now b new_sess_idx 0 st_r_m2 in
        new_session #oyrs_preds #now b new_sess_idx 0 ser_st;

        (new_sess_idx, send_m2_idx)
    )
    | _ -> error "r_send_m2: wrong message\n"
  )
  | _ -> error "r_send_m2: wrong session\n"

let find_auth_server_session_helper (svr:principal) (p:principal) :
  LCrypto (i:timestamp * si:nat * vi:nat * session_st) (pki oyrs_preds)
    (requires fun t0 -> True)
    (ensures fun t0 (i,si,vi,st) t1 -> t1 == t0 /\ i == trace_len t1 /\ valid_session i svr si vi st /\
                                    (match st with | AuthServerSession p' _ _ -> p = p' | _ -> False))
= let now = global_timestamp () in
  match find_session #oyrs_preds #now svr (fun si vi ser_st ->
    match parse_session_st ser_st with
    | Success (AuthServerSession p' _ _) -> p = p' | _ -> false
  ) with
  | Some (|si,vi,ser_st|) -> (
    match parse_session_st ser_st with
    | Success (AuthServerSession p sk us) -> (now,si,vi,(AuthServerSession p sk us))
    | _ -> error "find_auth_server_session_helper: wrong session\n"
  )
  | None -> error ("find_auth_server_session_helper: no session for " ^ p ^ " found")
#pop-options

#push-options "--z3rlimit 600"
let server_send_msg_3 srv msg2_idx =
  // receive and parse second message
  let (|now,b,ser_msg2|) = receive_i #oyrs_preds msg2_idx srv in

  match parse_msg ser_msg2 with
  | Success (Msg2 c a b' (|tag_ev_a,c_ev_a|) (|tag_ev_b,c_ev_b|)) -> (
    // TODO: should remove check, where some principal is compared with principal returned by "receive_i" function?
    if b <> b' then error "srv_send_m3: responder in message does not match with actual responder\n"
    else
      // look up auth sessions of initiator and responder, containg shared secrets with server
      let (now,_,_,(AuthServerSession _ k_as _)) = find_auth_server_session_helper srv a in
      let (_,_,_,(AuthServerSession _ k_bs _)) = find_auth_server_session_helper srv b in

      // decrypt parts of message encrypted by initiator and responder, respectively
      let ad_a = (string_to_bytes #oyrs_global_usage #now "ev1") in
      let c_ev_a:msg oyrs_global_usage now public = c_ev_a in
      match aead_dec #oyrs_global_usage #now #(get_label oyrs_key_usages k_as) k_as (string_to_bytes #oyrs_global_usage #now "iv") c_ev_a ad_a with
      | Success ser_ev_a -> (
        let ad_b = (string_to_bytes #oyrs_global_usage #now "ev2") in
        let c_ev_b:msg oyrs_global_usage now public = c_ev_b in
        match aead_dec #oyrs_global_usage #now #(get_label oyrs_key_usages k_bs) k_bs (string_to_bytes #oyrs_global_usage #now "iv") c_ev_b ad_b with
        | Success ser_ev_b -> (
          // parse the decrypted message parts
          let tagged_ser_ev_a:ser_encval now (get_label oyrs_key_usages k_as) = (|tag_ev_a,ser_ev_a|) in
          match parse_encval tagged_ser_ev_a with
          | Success (EncMsg1 c_a a_a b_a n_a) -> (
            parsed_encval_is_valid_lemma tagged_ser_ev_a;

            let tagged_ser_ev_b:ser_encval now (get_label oyrs_key_usages k_bs) = (|tag_ev_b,ser_ev_b|) in
            match parse_encval tagged_ser_ev_b with
            | Success (EncMsg2 c_b a_b b_b n_b) -> (
              parsed_encval_is_valid_lemma tagged_ser_ev_b;

              if c_a <> c_b || a_a <> a_b || b_a <> b_b then error "srv_send_m3: encrypted parts of initiator and responder do not match\n"
              // This should fix the attack in which the attacker impersonates the responder by replacing the responders name with his name in the unencrypted part
              else if a_a <> a || a_b <> a || b_a <> b || b_b <> b then error "srv_send_m3: principal names in encrypted parts do not match with principal names in unencrypted part\n"
              else if c_a <> c || c_b <> c then error "srv_send_m3: conversation id in encrypted parts does not match with conversation id in unencrypted part\n"
              else
                // generate shared conversation key between initiator and responder
                let prev = now in
                let (|now,k_ab|) = rand_gen #oyrs_preds (readers [P srv; P a; P b]) (aead_usage "sk_i_r") in

                // k_as publishable or aead_pred holds
                assert(is_publishable oyrs_global_usage now k_as
                  \/ aead_pred oyrs_usage_preds now "sk_i_srv" k_as ser_ev_a ad_a);
                // if k_as publishable, k_as readers flow to public
                assert(is_publishable oyrs_global_usage now k_as
                  ==> can_flow now (get_label oyrs_key_usages k_as) public);
                // k_as readable by responder and server
                assert(is_labeled oyrs_global_usage now k_as (readers [P a; P srv]));
                // k_as readers flow to public -> k_as readers corrupted
                publishable_readers_implies_corruption #now [P a; P srv];
                // k_as readers corrupted or aead_pred holds
                includes_corrupt_2_lemma now (P a) (P srv);
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ aead_pred oyrs_usage_preds now "sk_i_srv" k_as ser_ev_a ad_a);

                // if aead_pred holds, oyrs_aead_pred holds for some timestamp before now
                assert(aead_pred oyrs_usage_preds now "sk_i_srv" k_as ser_ev_a ad_a
                  ==> (exists i. later_than now i /\ oyrs_aead_pred i "sk_i_srv" k_as ser_ev_a ad_a));
                // k_as readers corrupted or oyrs_aead_pred holds for some timestamp before now
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ oyrs_aead_pred i "sk_i_srv" k_as ser_ev_a ad_a));

                // plug in definition of oyrs_aead_pred
                assert(exists i. (later_than now i /\ oyrs_aead_pred i "sk_i_srv" k_as ser_ev_a ad_a)
                  ==> (forall (t:string{CryptoLib.bytes_to_string ad_a = Success t}). can_aead_encrypt i "sk_i_srv" k_as (|t,ser_ev_a|) ad_a));
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. forall (t:string{CryptoLib.bytes_to_string ad_a = Success t}). later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|t,ser_ev_a|) ad_a));

                // tag_ev_a is concrete value for t
                assert(CryptoLib.bytes_to_string ad_a = Success tag_ev_a);
                // can_aead_encrypt holds for all t -> holds for concrete t
                can_aead_encrypt_encval_lemma now tag_ev_a (get_label oyrs_key_usages k_as) "sk_i_srv" k_as ser_ev_a ad_a;
                // if can_aead_encrypt holds for all t, it holds for tag_ev_a
                assert((exists i. forall (t:string{CryptoLib.bytes_to_string ad_a = Success t}). later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|t,ser_ev_a|) ad_a)
                  ==> (exists i. later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|tag_ev_a,ser_ev_a|) ad_a));
                // k_as readers corrupted or can_aead_encrypt holds for tag_ev_a
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|tag_ev_a,ser_ev_a|) ad_a));

                // prepare F* for rest of proof
                (*** NOTE: THIS LEMMA IS NOT PART OF THE PUBLIC DY* VERSION ***)
                readers_is_injective_2 a srv;
                parse_encval_lemma #now #(get_label oyrs_key_usages k_as) (|tag_ev_a,ser_ev_a|);
                assert(get_label oyrs_key_usages k_as == (readers [P a; P srv])
                  /\ _parse_encval (|tag_ev_a,ser_ev_a|) == Success (EncMsg1 c a b n_a));
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ get_label oyrs_key_usages k_as == (readers [P a; P srv]) /\ did_event_occur_before i a (event_initiate c a b srv n_a)));

                // if can_aead_encrypt holds for tag_ev_a, event_initiate occured before some timestamp before now
                assert((exists i. later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|tag_ev_a,ser_ev_a|) ad_a)
                  ==> (exists i. later_than now i /\ did_event_occur_before i a (event_initiate c a b srv n_a)));
                // k_as readers corrupted or event_initiate occured before some timestamp before now
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ did_event_occur_before i a (event_initiate c a b srv n_a)));

                // if event_initiate occured before some timestamp before now, it occured before now (AHOI, captain obvious)
                assert((exists i. later_than now i /\ did_event_occur_before i a (event_initiate c a b srv n_a))
                  ==> did_event_occur_before now a (event_initiate c a b srv n_a));
                // k_as readers corrupted or event_initiate occured before now
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ did_event_occur_before now a (event_initiate c a b srv n_a));

                // k_bs publishable or aead_pred holds
                assert(is_publishable oyrs_global_usage now k_bs
                  \/ aead_pred oyrs_usage_preds now "sk_r_srv" k_bs ser_ev_b ad_b);
                // if k_bs publishable, k_bs readers flow to public
                assert(is_publishable oyrs_global_usage now k_bs
                  ==> can_flow now (get_label oyrs_key_usages k_bs) public);
                // k_bs readable by responder and server
                assert(is_labeled oyrs_global_usage now k_bs (readers [P b; P srv]));
                // k_bs readers flow to public -> k_bs readers corrupted
                publishable_readers_implies_corruption #now [P b; P srv];
                // k_bs readers corrupted or aead_pred holds
                includes_corrupt_2_lemma now (P b) (P srv);
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ aead_pred oyrs_usage_preds now "sk_r_srv" k_bs ser_ev_b ad_b);

                // if aead_pred holds, oyrs_aead_pred holds for some timestamp before now
                assert(aead_pred oyrs_usage_preds now "sk_r_srv" k_bs ser_ev_b ad_b
                  ==> (exists i. later_than now i /\ oyrs_aead_pred i "sk_r_srv" k_bs ser_ev_b ad_b));
                // k_bs readers corrupted or oyrs_aead_pred holds for some timestamp before now
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ oyrs_aead_pred i "sk_r_srv" k_bs ser_ev_b ad_b));

                // plug in definition of oyrs_aead_pred
                assert(exists i. (later_than now i /\ oyrs_aead_pred i "sk_r_srv" k_bs ser_ev_b ad_b)
                  ==> (forall (t:string{CryptoLib.bytes_to_string ad_b = Success t}). can_aead_encrypt i "sk_r_srv" k_bs (|t,ser_ev_b|) ad_b));
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. forall (t:string{CryptoLib.bytes_to_string ad_b = Success t}). later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|t,ser_ev_b|) ad_b));

                // tag_ev_b is concrete value for t
                assert(CryptoLib.bytes_to_string ad_b = Success tag_ev_b);
                // can_aead_encrypt holds for all t -> holds for concrete t
                can_aead_encrypt_encval_lemma now tag_ev_b (get_label oyrs_key_usages k_bs) "sk_r_srv" k_bs ser_ev_b ad_b;
                // if can_aead_encrypt holds for all t, it holds for tag_ev_b
                assert((exists i. forall (t:string{CryptoLib.bytes_to_string ad_b = Success t}). later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|t,ser_ev_b|) ad_b)
                  ==> (exists i. later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|tag_ev_b,ser_ev_b|) ad_b));
                // k_bs readers corrupted or can_aead_encrypt holds for tag_ev_b
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|tag_ev_b,ser_ev_b|) ad_b));

                // prepare F* for rest of proof
                (*** NOTE: THIS LEMMA IS NOT PART OF THE PUBLIC DY* VERSION ***)
                readers_is_injective_2 b srv;
                parse_encval_lemma #now #(get_label oyrs_key_usages k_bs) (|tag_ev_b,ser_ev_b|);
                assert(get_label oyrs_key_usages k_bs == (readers [P b; P srv])
                  /\ _parse_encval (|tag_ev_b,ser_ev_b|) == Success (EncMsg2 c a b n_b));
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ get_label oyrs_key_usages k_bs == (readers [P b; P srv]) /\ did_event_occur_before i b (event_request_key c a b srv n_b)));

                // if can_aead_encrypt holds for tag_ev_b, event_request_key occured before some timestamp before now
                assert((exists i. later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|tag_ev_b,ser_ev_b|) ad_b)
                  ==> (exists i. later_than now i /\ did_event_occur_before i b (event_request_key c a b srv n_b)));
                // k_bs readers corrupted or event_request_key occured before some timestamp before now
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ did_event_occur_before i b (event_request_key c a b srv n_b)));

                // if event_request_key occured before some timestamp before now, it occured before now (AHOI, captain obvious)
                assert((exists i. later_than now i /\ did_event_occur_before i b (event_request_key c a b srv n_b))
                  ==> did_event_occur_before now b (event_request_key c a b srv n_b));
                // k_bs readers corrupted or event_request_key occured before now
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ did_event_occur_before now b (event_request_key c a b srv n_b));

                assert(((corrupt_id now (P a)) \/ (corrupt_id now (P srv)) \/ did_event_occur_before now a (event_initiate c a b srv n_a))
                  /\ ((corrupt_id now (P b)) \/ (corrupt_id now (P srv)) \/ did_event_occur_before now b (event_request_key c a b srv n_b)));
                assert((((corrupt_id now (P a)) \/ (corrupt_id now (P srv)) \/ did_event_occur_before now a (event_initiate c a b srv n_a))
                  /\ ((corrupt_id now (P b)) \/ (corrupt_id now (P srv)) \/ did_event_occur_before now b (event_request_key c a b srv n_b)))
                  ==> (((corrupt_id now (P a)) \/ (corrupt_id now (P srv)) \/ (corrupt_id now (P b)) \/ did_event_occur_before now a (event_initiate c a b srv n_a))
                  /\ ((corrupt_id now (P b)) \/ (corrupt_id now (P srv)) \/ (corrupt_id now (P a)) \/ did_event_occur_before now b (event_request_key c a b srv n_b))));
                assert((((corrupt_id now (P a)) \/ (corrupt_id now (P srv)) \/ (corrupt_id now (P b)) \/ did_event_occur_before now a (event_initiate c a b srv n_a))
                  /\ ((corrupt_id now (P b)) \/ (corrupt_id now (P srv)) \/ (corrupt_id now (P a)) \/ did_event_occur_before now b (event_request_key c a b srv n_b)))
                  ==> (corrupt_id now (P a)) \/ (corrupt_id now (P srv)) \/ (corrupt_id now (P b))
                  \/ (did_event_occur_before now a (event_initiate c a b srv n_a) /\ did_event_occur_before now b (event_request_key c a b srv n_b)));
                assert(was_rand_generated_before now k_ab (readers [P srv; P a; P b]) (aead_usage "sk_i_r"));

                // trigger event 'send key'
                let event = event_send_key c a b srv n_a n_b k_ab in
                assert(epred now srv event);
                trigger_event #oyrs_preds srv event;

                // create and send third message
                let ev3_i = EncMsg3_I n_a b k_ab in
                let now = global_timestamp () in
                can_flow_later prev now (readers [P a; P srv]) (readers [P a; P srv]);
                includes_can_flow_lemma now [P srv; P a; P b] [P a; P srv];
                assert(is_msg oyrs_global_usage now k_ab (get_label oyrs_key_usages k_as));
                assert(is_msg oyrs_global_usage prev n_a (get_label oyrs_key_usages k_as));
                assert(is_msg oyrs_global_usage now n_a (get_label oyrs_key_usages k_as));
                let (|tag_ev3_i,ser_ev3_i|) = serialize_encval now ev3_i (get_label oyrs_key_usages k_as) in
                let ad = (string_to_bytes #oyrs_global_usage #now "ev3_i") in
                assert(tag_ev3_i = "ev3_i");
                assert(was_rand_generated_before now k_ab (readers [P srv; P a; P b]) (aead_usage "sk_i_r"));
                assert(did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab));
                parse_serialize_encval_lemma now ev3_i (get_label oyrs_key_usages k_as);
                assert(can_aead_encrypt now "sk_i_srv" k_as (|tag_ev3_i,ser_ev3_i|) ad);
                let c_ev3_i = aead_enc #oyrs_global_usage #now #(get_label oyrs_key_usages k_as) k_as (string_to_bytes #oyrs_global_usage #now "iv") ser_ev3_i ad in

                let ev3_r = EncMsg3_R n_b a k_ab in
                can_flow_later prev now (readers [P b; P srv]) (readers [P b; P srv]);
                includes_can_flow_lemma now [P srv; P a; P b] [P b; P srv];
                assert(is_msg oyrs_global_usage now k_ab (get_label oyrs_key_usages k_bs));
                assert(is_msg oyrs_global_usage prev n_b (get_label oyrs_key_usages k_bs));
                assert(is_msg oyrs_global_usage now n_b (get_label oyrs_key_usages k_bs));
                let (|tag_ev3_r,ser_ev3_r|) = serialize_encval now ev3_r (get_label oyrs_key_usages k_bs) in
                let ad = (string_to_bytes #oyrs_global_usage #now "ev3_r") in
                assert(tag_ev3_r = "ev3_r");
                parse_serialize_encval_lemma now ev3_r (get_label oyrs_key_usages k_bs);
                assert(can_aead_encrypt now "sk_r_srv" k_bs (|tag_ev3_r,ser_ev3_r|) ad);
                let c_ev3_r = aead_enc #oyrs_global_usage #now #(get_label oyrs_key_usages k_bs) k_bs (string_to_bytes #oyrs_global_usage #now "iv") ser_ev3_r ad in

                let msg3:message now = Msg3 c (|tag_ev3_i,c_ev3_i|) (|tag_ev3_r,c_ev3_r|) in
                let ser_msg3 = serialize_msg now msg3 in

                let prev = now in
                let send_m3_idx = send #oyrs_preds #now srv b ser_msg3 in

                // store server session
                let new_sess_idx = new_session_number #oyrs_preds srv in
                let st_srv_sent_m3 = AuthServerSentMsg3 a b c n_a n_b k_ab in
                let now = global_timestamp () in
                assert(is_publishable oyrs_global_usage now c);
                assert(is_labeled oyrs_global_usage now k_as (readers [P a; P srv]));
                assert(is_labeled oyrs_global_usage now k_bs (readers [P b; P srv]));
                assert(is_msg oyrs_global_usage prev n_a (get_label oyrs_key_usages k_as));
                assert(is_msg oyrs_global_usage prev n_b (get_label oyrs_key_usages k_bs));
                assert(is_msg oyrs_global_usage prev n_a (get_label oyrs_key_usages k_as)
                  ==> is_msg oyrs_global_usage prev n_a (readers [P a; P srv]));
                assert(is_msg oyrs_global_usage prev n_b (get_label oyrs_key_usages k_bs)
                  ==> is_msg oyrs_global_usage prev n_b (readers [P b; P srv]));
                assert(can_flow prev (get_label oyrs_key_usages n_a) (readers [P a; P srv]));
                assert(can_flow prev (get_label oyrs_key_usages n_b) (readers [P b; P srv]));
                assert(later_than now prev);
                can_flow_later prev now (get_label oyrs_key_usages n_a) (readers [P a; P srv]);
                can_flow_later prev now (get_label oyrs_key_usages n_b) (readers [P b; P srv]);
                assert(can_flow now (get_label oyrs_key_usages n_a) (readers [P a; P srv]));
                assert(can_flow now (get_label oyrs_key_usages n_b) (readers [P b; P srv]));
                includes_can_flow_lemma now [P a; P srv] [P srv];
                includes_can_flow_lemma now [P b; P srv] [P srv];
                can_flow_transitive now (get_label oyrs_key_usages n_a) (readers [P a; P srv]) (readers [P srv]);
                can_flow_transitive now (get_label oyrs_key_usages n_b) (readers [P b; P srv]) (readers [P srv]);
                assert(can_flow now (get_label oyrs_key_usages n_a) (readers [P srv]));
                assert(can_flow now (get_label oyrs_key_usages n_b) (readers [P srv]));
                assert(is_valid oyrs_global_usage prev n_a);
                assert(is_valid oyrs_global_usage prev n_b);
                is_valid_later oyrs_global_usage prev now n_a;
                is_valid_later oyrs_global_usage prev now n_b;
                assert(is_valid oyrs_global_usage now n_a);
                assert(is_valid oyrs_global_usage now n_b);
                assert(can_flow now (get_label oyrs_key_usages n_a) (readers [P srv]) /\ is_valid oyrs_global_usage now n_a
                  ==> is_msg oyrs_global_usage now n_a (readers [P srv]));
                assert(can_flow now (get_label oyrs_key_usages n_b) (readers [P srv]) /\ is_valid oyrs_global_usage now n_b
                  ==> is_msg oyrs_global_usage now n_b (readers [P srv]));
                let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sent_m3 in
                new_session #oyrs_preds #now srv new_sess_idx 0 ser_st;

                (new_sess_idx, send_m3_idx)
            )
            | _ -> error "srv_send_m3: wrong responder encval\n"
          )
          | _ -> error "srv_send_m3: wrong initiator encval\n"
        )
        | Error e -> error ("srv_send_m3: decryption of responder part failed: " ^ e)
      )
      | Error e -> error ("srv_send_m3: decryption of initiator part failed: " ^ e)
  )
  | _ -> error "srv_send_m3: wrong message\n"

let responder_send_msg_4 b msg3_idx b_ii b_si =
  // get responder session
  let now = global_timestamp () in
  let (|b_vi,ser_st|) = get_session #oyrs_preds #now b b_si in
  let (|_,ser_init|) = get_session #oyrs_preds #now b b_ii in

  match (parse_session_st ser_st, parse_session_st ser_init) with
  | (Success (ResponderSentMsg2 srv k_bs a c n_b), Success (ResponderInit srv' k_bs')) -> (
    // receive and parse third message
    let (|_,srv'',ser_msg3|) = receive_i #oyrs_preds msg3_idx b in

    // TODO: should remove check, where some principal is compared with principal returned by "receive_i" function?
    if srv <> srv' || srv <> srv'' then error "r_send_m4: stored server does not match with actual server that sent the third message\n"
    else if k_bs <> k_bs' then error "r_send_m4: stored long term keys of responder do not match"
    else
      match parse_msg ser_msg3 with
      | Success (Msg3 c' (|tag_ev_a,c_ev_a|) (|tag_ev_b,c_ev_b|)) -> (
        if c <> c' then error "r_send_m4: conversation id in message does not match with the stored id\n"
        else
          // decrypt part of message intended for responder
          let now = global_timestamp () in
          let ad = (string_to_bytes #oyrs_global_usage #now "ev3_r") in
          match aead_dec #oyrs_global_usage #now #(get_label oyrs_key_usages k_bs) k_bs (string_to_bytes #oyrs_global_usage #now "iv") c_ev_b ad with
          | Success ser_ev_b -> (
            // parse the decrypted part
            let tagged_ser_ev_b:ser_encval now (get_label oyrs_key_usages k_bs) = (|tag_ev_b,ser_ev_b|) in
            match parse_encval tagged_ser_ev_b with
            | Success (EncMsg3_R n_b' a' k_ab) -> (
              parsed_encval_is_valid_lemma tagged_ser_ev_b;

              if n_b <> n_b' then error "r_send_m4: responder nonce in message does not match with the stored nonce\n"
              else if a <> a' then error "r_send_m4: stored initiator does not match with initiator in part encrypted for responder\n"
              else
                // k_bs publishable or aead_pred holds
                assert(is_publishable oyrs_global_usage now k_bs
                  \/ aead_pred oyrs_usage_preds now "sk_r_srv" k_bs ser_ev_b ad);
                // if k_bs publishable, k_bs readers flow to public
                assert(is_publishable oyrs_global_usage now k_bs
                  ==> can_flow now (get_label oyrs_key_usages k_bs) public);
                // k_bs readable by responder and server
                assert(is_labeled oyrs_global_usage now k_bs (readers [P b; P srv]));
                // k_bs readers flow to public -> k_bs readers corrupted
                publishable_readers_implies_corruption #now [P b; P srv];
                // k_bs readers corrupted or aead_pred holds
                includes_corrupt_2_lemma now (P b) (P srv);
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ aead_pred oyrs_usage_preds now "sk_r_srv" k_bs ser_ev_b ad);

                // if aead_pred holds, oyrs_aead_pred holds for some timestamp before now
                assert(aead_pred oyrs_usage_preds now "sk_r_srv" k_bs ser_ev_b ad
                  ==> (exists i. later_than now i /\ oyrs_aead_pred i "sk_r_srv" k_bs ser_ev_b ad));
                // k_bs readers corrupted or oyrs_aead_pred holds for some timestamp before now
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ oyrs_aead_pred i "sk_r_srv" k_bs ser_ev_b ad));

                // plug in definition of oyrs_aead_pred
                assert(exists i. (later_than now i /\ oyrs_aead_pred i "sk_r_srv" k_bs ser_ev_b ad)
                  ==> (forall (t:string{CryptoLib.bytes_to_string ad = Success t}). can_aead_encrypt i "sk_r_srv" k_bs (|t,ser_ev_b|) ad));
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. forall (t:string{CryptoLib.bytes_to_string ad = Success t}). later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|t,ser_ev_b|) ad));

                // tag_ev_b is concrete value for t
                assert(CryptoLib.bytes_to_string ad = Success tag_ev_b);
                // can_aead_encrypt holds for all t -> holds for concrete t
                can_aead_encrypt_encval_lemma now tag_ev_b (get_label oyrs_key_usages k_bs) "sk_r_srv" k_bs ser_ev_b ad;
                // if can_aead_encrypt holds for all t, it holds for tag_ev_b
                assert((exists i. forall (t:string{CryptoLib.bytes_to_string ad = Success t}). later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|t,ser_ev_b|) ad)
                  ==> (exists i. later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|tag_ev_b,ser_ev_b|) ad));
                // k_bs readers corrupted or can_aead_encrypt holds for tag_ev_b
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|tag_ev_b,ser_ev_b|) ad));

                // prepare F* for rest of proof
                (*** NOTE: THIS LEMMA IS NOT PART OF THE PUBLIC DY* VERSION ***)
                readers_is_injective_2 b srv;
                parse_encval_lemma #now #(get_label oyrs_key_usages k_bs) (|tag_ev_b,ser_ev_b|);
                assert(get_label oyrs_key_usages k_bs == (readers [P b; P srv])
                  /\ _parse_encval (|tag_ev_b,ser_ev_b|) == Success (EncMsg3_R n_b a k_ab));
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ get_label oyrs_key_usages k_bs == (readers [P b; P srv]) /\ (exists c n_a. did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))));

                // if can_aead_encrypt holds for tag_ev_b, event_send_key occured before some timestamp before now
                assert((exists i. later_than now i /\ can_aead_encrypt i "sk_r_srv" k_bs (|tag_ev_b,ser_ev_b|) ad)
                  ==> (exists i. later_than now i /\ (exists c n_a. did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))));
                // k_bs readers corrupted or event_send_key occured before some timestamp before now
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ (exists c n_a. did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))));

                // if event_send_key occured before some timestamp before now, it occured before now (AHOI, captain obvious)
                assert((exists i c n_a. later_than now i /\ did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))
                  ==> (exists c n_a. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));
                // k_bs readers corrupted or event_send_key occured before now
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists c n_a. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));

                // trigger event 'forward key'
                let prev = now in
                let event = event_forward_key c a b srv n_b k_ab in
                trigger_event #oyrs_preds b event;

                // create and send fourth message
                let msg4:message now = Msg4 c (|tag_ev_a,c_ev_a|) in
                let ser_msg4 = serialize_msg now msg4 in

                let send_m4_idx = send #oyrs_preds #now b a ser_msg4 in

                // update responder session
                let st_r_sent_m4 = ResponderSentMsg4 srv a k_ab in
                let now = global_timestamp () in
                assert(is_msg oyrs_global_usage prev k_ab (get_label oyrs_key_usages k_bs));
                assert(is_labeled oyrs_global_usage prev k_bs (readers [P b; P srv]));
                assert(is_msg oyrs_global_usage prev k_ab (readers [P b; P srv]));
                assert(is_msg oyrs_global_usage prev k_ab (readers [P b; P srv])
                  ==> can_flow prev (get_label oyrs_key_usages k_ab) (readers [P b; P srv]) /\ is_valid oyrs_global_usage prev k_ab);
                can_flow_later prev now (get_label oyrs_key_usages k_ab) (readers [P b; P srv]);
                is_valid_later oyrs_global_usage prev now k_ab;
                assert(can_flow prev (get_label oyrs_key_usages k_ab) (readers [P b; P srv]) /\ is_valid oyrs_global_usage prev k_ab);
                assert(can_flow prev (get_label oyrs_key_usages k_ab) (readers [P b; P srv]) /\ is_valid oyrs_global_usage prev k_ab
                  ==> is_msg oyrs_global_usage now k_ab (readers [P b; P srv]));
                includes_can_flow_lemma now [P b; P srv] [P b];
                can_flow_transitive now (get_label oyrs_key_usages k_ab) (readers [P b; P srv]) (readers [P b]);
                assert(is_msg oyrs_global_usage now k_ab (readers [P b]));
                // prove responder or server corrupt or k_ab is labeled with server, initiator, responder
                assert((exists c n_a. did_event_occur_before prev srv (event_send_key c a b srv n_a n_b k_ab))
                  ==> (exists c n_a. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));
                assert((corrupt_id now (P b)) \/ (corrupt_id now (P srv))
                  \/ (exists c n_a. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));
                assert((exists c n_a. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab))
                  ==> was_rand_generated_before now k_ab (readers [P srv; P a; P b]) (aead_usage "sk_i_r"));
                rand_is_secret #oyrs_global_usage #now #(readers [P srv; P a; P b]) #(aead_usage "sk_i_r") k_ab;
                let ser_st = serialize_session_st now b b_si b_vi st_r_sent_m4 in
                update_session #oyrs_preds #now b b_si b_vi ser_st;

                send_m4_idx
            )
            | _ -> error "r_send_m4: wrong encval\n"
          )
          | Error e -> error ("r_send_m4: decryption of part intended for responder failed: " ^ e)
      )
      | _ -> error "r_send_m4: wrong message\n"
  )
  | _ -> error "r_send_m4: wrong sessions\n"

let initiator_recv_msg_4 a msg4_idx a_ii a_si =
  // get initiator session
  let now = global_timestamp () in
  let (|a_vi,ser_st|) = get_session #oyrs_preds #now a a_si in
  let (|_,ser_init|) = get_session #oyrs_preds #now a a_ii in

  match (parse_session_st ser_st, parse_session_st ser_init) with
  | (Success (InitiatorSentMsg1 srv k_as b c n_a), Success (InitiatorInit srv' k_as' b')) -> (
    // receive and parse fourth message
    let (|_,b'',ser_msg4|) = receive_i #oyrs_preds msg4_idx a in

    // TODO: should remove check, where some principal is compared with principal returned by "receive_i" function?
    if b <> b' || b <> b'' then error "i_recv_m4: stored responder does not match with actual responder that sent the fourth message\n"
    else if srv <> srv' then error "i_recv_m4: stored servers do not match"
    else if k_as <> k_as' then error "i_recv_m4: stored long term keys of initiator do not match"
    else
      match parse_msg ser_msg4 with
      | Success (Msg4 c' (|tag_ev_a,c_ev_a|)) -> (
        if c <> c' then error "i_recv_m4: conversation id in message does not match with the stored id\n"
        else
          // decrypt part of message intended for initiator
          let now = global_timestamp () in
          let ad = (string_to_bytes #oyrs_global_usage #now "ev3_i") in
          match aead_dec #oyrs_global_usage #now #(get_label oyrs_key_usages k_as) k_as (string_to_bytes #oyrs_global_usage #now "iv") c_ev_a ad with
          | Success ser_ev_a -> (
            // parse the decrypted part
            let tagged_ser_ev_a:ser_encval now (get_label oyrs_key_usages k_as) = (|tag_ev_a,ser_ev_a|) in
            match parse_encval tagged_ser_ev_a with
            | Success (EncMsg3_I n_a' b' k_ab) -> (
              parsed_encval_is_valid_lemma tagged_ser_ev_a;

              if n_a <> n_a' then error "i_recv_m4: initiator nonce in message does not match with the stored nonce\n"
              else if b <> b' then error "i_recv_m4: stored responder does not match with responder in part encrypted for initiator\n"
              else
                // k_as publishable or aead_pred holds
                assert(is_publishable oyrs_global_usage now k_as
                  \/ aead_pred oyrs_usage_preds now "sk_i_srv" k_as ser_ev_a ad);
                // if k_as publishable, k_as readers flow to public
                assert(is_publishable oyrs_global_usage now k_as
                  ==> can_flow now (get_label oyrs_key_usages k_as) public);
                // k_as readable by responder and server
                assert(is_labeled oyrs_global_usage now k_as (readers [P a; P srv]));
                // k_as readers flow to public -> k_as readers corrupted
                publishable_readers_implies_corruption #now [P a; P srv];
                // k_as readers corrupted or aead_pred holds
                includes_corrupt_2_lemma now (P a) (P srv);
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ aead_pred oyrs_usage_preds now "sk_i_srv" k_as ser_ev_a ad);

                // if aead_pred holds, oyrs_aead_pred holds for some timestamp before now
                assert(aead_pred oyrs_usage_preds now "sk_i_srv" k_as ser_ev_a ad
                  ==> (exists i. later_than now i /\ oyrs_aead_pred i "sk_i_srv" k_as ser_ev_a ad));
                // k_as readers corrupted or oyrs_aead_pred holds for some timestamp before now
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ oyrs_aead_pred i "sk_i_srv" k_as ser_ev_a ad));

                // plug in definition of oyrs_aead_pred
                assert(exists i. (later_than now i /\ oyrs_aead_pred i "sk_i_srv" k_as ser_ev_a ad)
                  ==> (forall (t:string{CryptoLib.bytes_to_string ad = Success t}). can_aead_encrypt i "sk_i_srv" k_as (|t,ser_ev_a|) ad));
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. forall (t:string{CryptoLib.bytes_to_string ad = Success t}). later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|t,ser_ev_a|) ad));

                // tag_ev_a is concrete value for t
                assert(CryptoLib.bytes_to_string ad = Success tag_ev_a);
                // can_aead_encrypt holds for all t -> holds for concrete t
                can_aead_encrypt_encval_lemma now tag_ev_a (get_label oyrs_key_usages k_as) "sk_i_srv" k_as ser_ev_a ad;
                // if can_aead_encrypt holds for all t, it holds for tag_ev_a
                assert((exists i. forall (t:string{CryptoLib.bytes_to_string ad = Success t}). later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|t,ser_ev_a|) ad)
                  ==> (exists i. later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|tag_ev_a,ser_ev_a|) ad));
                // k_as readers corrupted or can_aead_encrypt holds for tag_ev_a
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|tag_ev_a,ser_ev_a|) ad));

                // prepare F* for rest of proof
                (*** NOTE: THIS LEMMA IS NOT PART OF THE PUBLIC DY* VERSION ***)
                readers_is_injective_2 a srv;
                parse_encval_lemma #now #(get_label oyrs_key_usages k_as) (|tag_ev_a,ser_ev_a|);
                assert(get_label oyrs_key_usages k_as == (readers [P a; P srv])
                  /\ _parse_encval (|tag_ev_a,ser_ev_a|) == Success (EncMsg3_I n_a b k_ab));
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ get_label oyrs_key_usages k_as == (readers [P a; P srv]) /\ (exists c n_b. did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))));

                // if can_aead_encrypt holds for tag_ev_a, event_send_key occured before some timestamp before now
                assert((exists i. later_than now i /\ can_aead_encrypt i "sk_i_srv" k_as (|tag_ev_a,ser_ev_a|) ad)
                  ==> (exists i. later_than now i /\ (exists c n_b. did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))));
                // k_as readers corrupted or event_send_key occured before some timestamp before now
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists i. later_than now i /\ (exists c n_b. did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))));

                // if event_send_key occured before some timestamp before now, it occured before now (AHOI, captain obvious)
                assert((exists i c n_b. later_than now i /\ did_event_occur_before i srv (event_send_key c a b srv n_a n_b k_ab))
                  ==> (exists c n_b. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));
                // k_as readers corrupted or event_send_key occured before now
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists c n_b. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));

                // trigger event 'recv key'
                let prev = now in
                let event = event_recv_key c a b srv n_a k_ab in
                trigger_event #oyrs_preds a event;

                // update initiator session
                let st_i_rcvd_m4 = InitiatorRecvedMsg4 srv b k_ab in
                let now = global_timestamp () in
                assert(is_msg oyrs_global_usage prev k_ab (get_label oyrs_key_usages k_as));
                assert(is_labeled oyrs_global_usage prev k_as (readers [P a; P srv]));
                assert(is_msg oyrs_global_usage prev k_ab (readers [P a; P srv]));
                assert(is_msg oyrs_global_usage prev k_ab (readers [P a; P srv])
                  ==> can_flow prev (get_label oyrs_key_usages k_ab) (readers [P a; P srv]) /\ is_valid oyrs_global_usage prev k_ab);
                can_flow_later prev now (get_label oyrs_key_usages k_ab) (readers [P a; P srv]);
                is_valid_later oyrs_global_usage prev now k_ab;
                assert(can_flow prev (get_label oyrs_key_usages k_ab) (readers [P a; P srv]) /\ is_valid oyrs_global_usage prev k_ab);
                assert(can_flow prev (get_label oyrs_key_usages k_ab) (readers [P a; P srv]) /\ is_valid oyrs_global_usage prev k_ab
                  ==> is_msg oyrs_global_usage now k_ab (readers [P a; P srv]));
                includes_can_flow_lemma now [P a; P srv] [P a];
                can_flow_transitive now (get_label oyrs_key_usages k_ab) (readers [P a; P srv]) (readers [P a]);
                assert(is_msg oyrs_global_usage now k_ab (readers [P a]));
                // prove responder or server corrupt or k_ab is labeled with server, initiator, responder
                assert((exists c n_b. did_event_occur_before prev srv (event_send_key c a b srv n_a n_b k_ab))
                  ==> (exists c n_b. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));
                assert((corrupt_id now (P a)) \/ (corrupt_id now (P srv))
                  \/ (exists c n_b. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab)));
                assert((exists c n_b. did_event_occur_before now srv (event_send_key c a b srv n_a n_b k_ab))
                  ==> was_rand_generated_before now k_ab (readers [P srv; P a; P b]) (aead_usage "sk_i_r"));
                rand_is_secret #oyrs_global_usage #now #(readers [P srv; P a; P b]) #(aead_usage "sk_i_r") k_ab;
                let ser_st = serialize_session_st now a a_si a_vi st_i_rcvd_m4 in
                update_session #oyrs_preds #now a a_si a_vi ser_st;

                ()
            )
            | _ -> error "i_recv_m4: wrong encval\n"
          )
          | Error e -> error ("i_recv_m4: decryption of part intended for initiator failed: " ^ e)
      )
      | _ -> error "i_recv_m4: wrong message\n"
  )
  | _ -> error "i_recv_m4: wrong sessions\n"
#pop-options
