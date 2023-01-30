module OYRS.SecurityProps


friend LabeledPKI


let principals_and_conv_key_stored_in_auth_server_state
  server
  set_state_idx
  vv
  server_state
  state_session_idx
  initiator
  responder
  conv_key
=
  state_was_set_at set_state_idx server vv server_state /\
  state_session_idx < Seq.Base.length server_state /\
  (
    let state_session = Seq.index server_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match OYRS.Sessions.parse_session_st ser_st with
     | Success (AuthServerSentMsg3 a b c n_a n_b k_ab) -> (
       a = initiator /\
       b = responder /\
       k_ab = conv_key
     )
     | _ -> False
    )
    | _ -> False
  )

let responder_and_server_and_conv_key_stored_in_initiator_state
  initiator
  set_state_idx
  vv
  init_state
  state_session_idx
  responder
  server
  conv_key
=
  state_was_set_at set_state_idx initiator vv init_state /\
  state_session_idx < Seq.Base.length init_state /\
  (
    let state_session = Seq.index init_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match OYRS.Sessions.parse_session_st ser_st with
     | Success (InitiatorRecvedMsg4 srv b k_ab) -> (
       srv = server /\
       b = responder /\
       k_ab = conv_key
     )
     | _ -> False
    )
    | _ -> False
  )

let initiator_and_server_and_conv_key_stored_in_responder_state
  responder
  set_state_idx
  vv
  resp_state
  state_session_idx
  initiator
  server
  conv_key
=
  state_was_set_at set_state_idx responder vv resp_state /\
  state_session_idx < Seq.Base.length resp_state /\
  (
    let state_session = Seq.index resp_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match OYRS.Sessions.parse_session_st ser_st with
     | Success (ResponderSentMsg4 srv a k_ab) -> (
       srv = server /\
       a = initiator /\
       k_ab = conv_key
     )
     | _ -> False
    )
    | _ -> False
  )

let conv_key_stored_in_auth_server_state_is_secret
  server
  set_state_idx
  vv
  server_state
  state_session_idx
  initiator
  responder
  conv_key
=
  match LabeledPKI.parse_session_st server_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match OYRS.Sessions.parse_session_st ser_st with
    | Success (AuthServerSentMsg3 a b c n_a n_b k_ab) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      secrecy_lemma #(pki oyrs_preds) conv_key
    )
    | _ -> ()
  )
  | _ -> ()

let conv_key_stored_in_initiator_state_is_secret
  initiator
  set_state_idx
  vv
  init_state
  state_session_idx
  responder
  server
  conv_key
=
  match LabeledPKI.parse_session_st init_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match OYRS.Sessions.parse_session_st ser_st with
    | Success (InitiatorRecvedMsg4 srv b k_ab) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      assert(OYRS.Sessions.valid_session now initiator state_session_idx vv.[state_session_idx] (InitiatorRecvedMsg4 srv b k_ab));
      assert((corrupt_id now (P initiator) \/ corrupt_id now (P server) \/ corrupt_id now (P responder) \/ is_labeled now k_ab (readers [P server; P initiator; P responder])));
      secrecy_lemma #(pki oyrs_preds) conv_key
    )
    | _ -> ()
  )
  | _ -> ()

let conv_key_stored_in_responder_state_is_secret
  responder
  set_state_idx
  vv
  resp_state
  state_session_idx
  initiator
  server
  conv_key
=
  match LabeledPKI.parse_session_st resp_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match OYRS.Sessions.parse_session_st ser_st with
    | Success (ResponderSentMsg4 srv a k_ab) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      secrecy_lemma #(pki oyrs_preds) conv_key
    )
    | _ -> ()
  )
  | _ -> ()

let initiator_authentication i = ()

let responder_authentication i = ()
