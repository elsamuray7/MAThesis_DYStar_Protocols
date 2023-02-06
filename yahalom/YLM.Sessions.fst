module YLM.Sessions


let serialize_session_st i p si vi st =
  let l = readers [V p si vi] in
  match st with
  | AuthServerSession pri k_pri_srv ->
    let tag = M.str_to_bytes #i "srv_sess" in
    let pri_bytes = M.str_to_bytes #i pri in
    LC.can_flow_transitive i (LC.get_label M.ylm_key_usages k_pri_srv) (readers [P p]) l;
    assert(M.is_msg i k_pri_srv l); // required
    M.concat #i #l tag (M.concat #i #l pri_bytes k_pri_srv)
  | PKeySession srv k_ps ->
    let tag = M.str_to_bytes #i "p_key_sess" in
    let srv_bytes = M.str_to_bytes #i srv in
    M.concat #i #l tag (M.concat #i #l srv_bytes k_ps)
  | InitiatorSentMsg1 b n_a ->
    let tag = M.str_to_bytes #i "i_sent_m1" in
    let b_bytes = M.str_to_bytes #i b in
    M.concat #i #l tag (M.concat #i #l b_bytes n_a)
  | ResponderSentMsg2 a srv n_b ->
    let tag = M.str_to_bytes #i "r_sent_m2" in
    let a_bytes = M.str_to_bytes #i a in
    let srv_bytes = M.str_to_bytes #i srv in
    M.concat #i #l tag (M.concat #i #l a_bytes (M.concat #i #l srv_bytes n_b))
  | AuthServerSentMsg3 a b k_ab ->
    let tag = M.str_to_bytes #i "srv_sent_m3" in
    let a_bytes = M.str_to_bytes #i a in
    let b_bytes = M.str_to_bytes #i b in
    M.concat #i #l tag (M.concat #i #l a_bytes (M.concat #i #l b_bytes k_ab))
  | InitiatorSentMsg4 b srv k_ab ->
    let tag = M.str_to_bytes #i "i_sent_m4" in
    let b_bytes = M.str_to_bytes #i b in
    let srv_bytes = M.str_to_bytes #i srv in
    LC.can_flow_transitive i (LC.get_label M.ylm_key_usages k_ab) (readers [P p]) l;
    M.concat #i #l tag (M.concat #i #l b_bytes (M.concat #i #l srv_bytes k_ab))
  | ResponderRecvedMsg4 a srv k_ab ->
    let tag = M.str_to_bytes #i "r_rcvd_m4" in
    let a_bytes = M.str_to_bytes #i a in
    let srv_bytes = M.str_to_bytes #i srv in
    LC.can_flow_transitive i (LC.get_label M.ylm_key_usages k_ab) (readers [P p]) l;
    M.concat #i #l tag (M.concat #i #l a_bytes (M.concat #i #l srv_bytes k_ab))

let parse_session_st sst =
  split sst `bind` (fun (tag_bytes, rest) ->
  bytes_to_string tag_bytes `bind` (fun tag ->
  match tag with
  | "srv_sess" ->
    split rest `bind` (fun (p_bytes, k_ps) ->
    bytes_to_string p_bytes `bind` (fun p ->
    Success (AuthServerSession p k_ps)))
  | "p_key_sess" ->
    split rest `bind` (fun (srv_bytes, k_ps) ->
    bytes_to_string srv_bytes `bind` (fun srv ->
    Success (PKeySession srv k_ps)))
  | "i_sent_m1" ->
    split rest `bind` (fun (b_bytes, n_a) ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (InitiatorSentMsg1 b n_a)))
  | "r_sent_m2" ->
    split rest `bind` (fun (a_bytes, rest) ->
    split rest `bind` (fun (srv_bytes, n_b) ->
    bytes_to_string a_bytes `bind` (fun a ->
    bytes_to_string srv_bytes `bind` (fun srv ->
    Success (ResponderSentMsg2 a srv n_b)))))
  | "srv_sent_m3" ->
    split rest `bind` (fun (a_bytes, rest) ->
    split rest `bind` (fun (b_bytes, k_ab) ->
    bytes_to_string a_bytes `bind` (fun a ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (AuthServerSentMsg3 a b k_ab)))))
  | "i_sent_m4" ->
    split rest `bind` (fun (b_bytes, rest) ->
    split rest `bind` (fun (srv_bytes, k_ab) ->
    bytes_to_string b_bytes `bind` (fun b ->
    bytes_to_string srv_bytes `bind` (fun srv ->
    Success (InitiatorSentMsg4 b srv k_ab)))))
  | "r_rcvd_m4" ->
    split rest `bind` (fun (a_bytes, rest) ->
    split rest `bind` (fun (srv_bytes, k_ab) ->
    bytes_to_string a_bytes `bind` (fun a ->
    bytes_to_string srv_bytes `bind` (fun srv ->
    Success (ResponderRecvedMsg4 a srv k_ab)))))
  | t -> Error ("[parse_session_st] invalid tag: " ^ t)
  ))

let parse_serialize_session_st_lemma i p si vi st =
  let l = readers [V p si vi] in
  match st with
  | AuthServerSession pri k_pri_srv ->
    LC.can_flow_transitive i (LC.get_label M.ylm_key_usages k_pri_srv) (readers [P p]) l
  | InitiatorSentMsg4 b srv k_ab ->
    LC.can_flow_transitive i (LC.get_label M.ylm_key_usages k_ab) (readers [P p]) l
  | ResponderRecvedMsg4 a srv k_ab ->
    LC.can_flow_transitive i (LC.get_label M.ylm_key_usages k_ab) (readers [P p]) l
  | _ -> ()
