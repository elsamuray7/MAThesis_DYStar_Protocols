module YLM.SecurityProps


friend LabeledPKI


let auth_server_state_contains_principals_and_comm_key server set_state_idx vv server_state
  state_session_idx initiator responder comm_key =
  state_was_set_at set_state_idx server vv server_state /\
  state_session_idx < Seq.Base.length server_state /\
  (
    let state_session = Seq.index server_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match YLM.Sessions.parse_session_st ser_st with
      | Success (AuthServerSentMsg3 a b k_ab) -> (
        a = initiator /\
        b = responder /\
        k_ab = comm_key
      )
      | _ -> False
    )
    | _ -> False
  )

let initiator_state_contains_responder_server_and_comm_key initiator set_state_idx vv
  init_state state_session_idx responder server comm_key =
  state_was_set_at set_state_idx initiator vv init_state /\
  state_session_idx < Seq.Base.length init_state /\
  (
    let state_session = Seq.index init_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match YLM.Sessions.parse_session_st ser_st with
      | Success (InitiatorSentMsg4 b srv k_ab) -> (
        b = responder /\
        srv = server /\
        k_ab = comm_key
      )
      | _ -> False
    )
    | _ -> False
  )

let responder_state_contains_initiator_server_and_comm_key responder set_state_idx vv
  resp_state state_session_idx initiator server comm_key =
  state_was_set_at set_state_idx responder vv resp_state /\
  state_session_idx < Seq.Base.length resp_state /\
  (
    let state_session = Seq.index resp_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match YLM.Sessions.parse_session_st ser_st with
      | Success (ResponderRecvedMsg4 a srv k_ab) -> (
        a = initiator /\
        srv = server /\
        k_ab = comm_key
      )
      | _ -> False
    )
    | _ -> False
  )

let auth_server_comm_key_is_secret server set_state_idx vv server_state state_session_idx
  initiator responder comm_key =
  match LabeledPKI.parse_session_st server_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match YLM.Sessions.parse_session_st ser_st with
    | Success (AuthServerSentMsg3 a b k_ab) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      secrecy_lemma #(pki ylm_preds) comm_key
    )
    | _ -> ()
  )
  | _ -> ()

let initiator_comm_key_is_secret initiator set_state_idx vv init_state state_session_idx
  responder server comm_key =
  match LabeledPKI.parse_session_st init_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match YLM.Sessions.parse_session_st ser_st with
    | Success (InitiatorSentMsg4 b srv k_ab) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      secrecy_lemma #(pki ylm_preds) comm_key
    )
    | _ -> ()
  )
  | _ -> ()

let responder_comm_key_is_secret responder set_state_idx vv resp_state state_session_idx
  initiator server comm_key =
  match LabeledPKI.parse_session_st resp_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match YLM.Sessions.parse_session_st ser_st with
    | Success (ResponderRecvedMsg4 a srv k_ab) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      secrecy_lemma #(pki ylm_preds) comm_key
    )
    | _ -> ()
  )
  | _ -> ()

let initiator_authentication i = ()

let responder_authentication i = ()
