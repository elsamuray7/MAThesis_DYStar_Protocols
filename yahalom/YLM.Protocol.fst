module YLM.Protocol


let new_lt_key_session p srv =
  let (|i,k_ps|) = rand_gen #ylm_preds (readers [P p; P srv]) (aead_usage "YLM.lt_key") in

  let new_sess_idx = new_session_number #ylm_preds p in
  let st_key_sess = PKeySession srv k_ps in
  let now = global_timestamp () in
  let ser_st = serialize_session_st now p new_sess_idx 0 st_key_sess in

  new_session #ylm_preds #now p new_sess_idx 0 ser_st;

  print_string ("new long term key session of " ^ p ^ " with " ^ srv ^ "\n");

  ((|i,k_ps|), new_sess_idx)

let install_lt_key_at_auth_server #i srv p k_ps =
  let new_sess_idx = new_session_number #ylm_preds srv in
  let st_srv_sess = AuthServerSession p k_ps in
  let now = global_timestamp () in
  is_valid_later ylm_global_usage i now k_ps;
  assert(can_flow now (get_label ylm_key_usages k_ps) (readers [P srv]));
  let ser_st = serialize_session_st now srv new_sess_idx 0 st_srv_sess in

  print_string ("installed long term key of " ^ p ^ " at " ^ srv ^ "\n");

  new_session #ylm_preds #now srv new_sess_idx 0 ser_st
