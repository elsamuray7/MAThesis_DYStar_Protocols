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

let conv_key_is_secret
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
