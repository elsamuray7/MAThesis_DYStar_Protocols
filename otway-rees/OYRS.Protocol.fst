module OYRS.Protocol


let initiator_init a srv b =
  let (|i,k_as|) = rand_gen #oyrs_preds (readers [P a; P srv]) (aead_usage "sk_i_srv") in
  let new_sess_idx = new_session_number #oyrs_preds a in
  let st_i_init = InitiatorInit srv k_as b in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now a new_sess_idx 0 st_i_init in
  new_session #oyrs_preds #now a new_sess_idx 0 ser_st;
  (|i,k_as|)

let responder_init b srv =
  let (|i,k_bs|) = rand_gen #oyrs_preds (readers [P b; P srv]) (aead_usage "sk_r_srv") in
  let new_sess_idx = new_session_number #oyrs_preds b in
  let st_r_init = ResponderInit srv k_bs in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now b new_sess_idx 0 st_r_init in
  new_session #oyrs_preds #now b new_sess_idx 0 ser_st;
  (|i,k_bs|)

let install_sk_at_auth_server #i srv p sk =
  let new_sess_idx = new_session_number #oyrs_preds srv in
  let st_srv_sess = AuthServerSession p sk in
  let now = global_timestamp () in

  // Prove that sk can flow to srv at now
  can_flow_later i now (readers [P p; P srv]) (readers [P p; P srv]);
  is_valid_later oyrs_global_usage i now sk;
  can_flow_transitive now (get_label oyrs_key_usages sk) (readers [P p; P srv]) (readers [P srv]);
  let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sess in

  new_session #oyrs_preds #now srv new_sess_idx 0 ser_st
