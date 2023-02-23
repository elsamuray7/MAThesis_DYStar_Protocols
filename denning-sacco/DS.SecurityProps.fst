module DS.SecurityProps


friend LabeledPKI


let initiator_state_contains_responder_server_and_comm_key initiator set_state_idx vv
  initiator_state state_session_idx responder server comm_key =
  state_was_set_at set_state_idx initiator vv initiator_state /\
  state_session_idx < Seq.Base.length initiator_state /\
  (
    let state_session = Seq.index initiator_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match DS.Sessions.parse_session_st ser_st with
     | Success (InitiatorSentMsg3 b srv ck) -> (
       b = responder /\
       srv = server /\
       ck = comm_key
     )
     | _ -> False
    )
    | _ -> False
  )

let responder_state_contains_initiator_server_and_comm_key responder set_state_idx vv
  responder_state state_session_idx initiator server comm_key =
  state_was_set_at set_state_idx responder vv responder_state /\
  state_session_idx < Seq.Base.length responder_state /\
  (
    let state_session = Seq.index responder_state state_session_idx in
    match LabeledPKI.parse_session_st state_session with
    | Success (APP ser_st) -> (
      match DS.Sessions.parse_session_st ser_st with
     | Success (ResponderRecvedMsg3 a srv ck) -> (
       a = initiator /\
       srv = server /\
       ck = comm_key
     )
     | _ -> False
    )
    | _ -> False
  )

let initiator_comm_key_is_secret initiator set_state_idx vv initiator_state state_session_idx
  responder server comm_key =
  match LabeledPKI.parse_session_st initiator_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match DS.Sessions.parse_session_st ser_st with
    | Success (InitiatorSentMsg3 b srv ck) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      secrecy_join_label_lemma #(pki ds_preds) comm_key
    )
    | _ -> ()
  )
  | _ -> ()

let responder_comm_key_is_secret responder set_state_idx vv responder_state state_session_idx
  initiator server comm_key =
  match LabeledPKI.parse_session_st responder_state.[state_session_idx] with
  | Success (APP ser_st) -> (
    match DS.Sessions.parse_session_st ser_st with
    | Success (ResponderRecvedMsg3 a srv ck) -> (
      let now = global_timestamp () in
      assert(later_than now set_state_idx);
      secrecy_join_label_lemma #(pki ds_preds) comm_key
    )
    | _ -> ()
  )
  | _ -> ()

let responder_comm_key_is_not_replay i = ()

let mutual_authentication i j = ()
