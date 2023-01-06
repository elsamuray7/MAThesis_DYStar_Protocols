module OYRS.Sessions


let valid_session i p si vi st =
  match st with
  | AuthServerSession pri k_pri_srv -> MSG.is_msg i k_pri_srv (readers [P p])
  | InitiatorInit srv k_as b -> is_labeled i k_as (readers [P p; P srv])
  | ResponderInit srv k_bs -> is_labeled i k_bs (readers [P p; P srv])
  | InitiatorSentMsg1 srv k_as b c n_a ->
    is_labeled i k_as (readers [P p; P srv]) /\
    is_labeled i c public /\
    is_labeled i n_a (readers [P p; P srv])
  | ResponderSentMsg2 srv k_bs a c n_b ->
    is_labeled i k_bs (readers [P p; P srv]) /\
    MSG.is_msg i c public /\
    is_labeled i n_b (readers [P p; P srv])
  | AuthServerSentMsg3 a b c n_a n_b k_ab ->
    MSG.is_msg i c public /\
    MSG.is_msg i n_a (readers [P p]) /\
    MSG.is_msg i n_b (readers [P p]) /\
    is_labeled i k_ab (readers [P p; P a; P b])
  | ResponderSentMsg4 srv a k_ab -> MSG.is_msg i k_ab (readers [P p])
  | InitiatorRecvedMsg4 srv b k_ab -> MSG.is_msg i k_ab (readers [P p])

let serialize_session_st i p si vi st =
  match st with
  | AuthServerSession pri k_pri_srv ->
    let tag = str_to_bytes #i "srv_sess" in
    let pri_bytes = str_to_bytes #i pri in
    let _ = assert(valid_session i p si vi st) in
    let _ = assert(MSG.is_msg i k_pri_srv (readers [P p])) in
    LC.can_flow_transitive i (LC.get_label MSG.oyrs_key_usages k_pri_srv) (readers [P p]) (readers [V p si vi]);
    // TODO: why assert needed??
    let _ = assert(MSG.is_msg i k_pri_srv (readers [V p si vi])) in
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) pri_bytes k_pri_srv)
  | InitiatorInit srv k_as b ->
    let tag = str_to_bytes #i "i_init" in
    let srv_bytes = str_to_bytes #i srv in
    let b_bytes = str_to_bytes #i b in
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) srv_bytes (concat #i #(readers [V p si vi]) k_as b_bytes))
  | ResponderInit srv k_bs ->
    let tag = str_to_bytes #i "r_init" in
    let srv_bytes = str_to_bytes #i srv in
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) srv_bytes k_bs)
  | InitiatorSentMsg1 srv k_as b c n_a ->
    let tag = str_to_bytes #i "i_sent_m1" in
    let srv_bytes = str_to_bytes #i srv in
    let b_bytes = str_to_bytes #i b in
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) srv_bytes (concat #i #(readers [V p si vi]) k_as (concat #i #(readers [V p si vi]) b_bytes (concat #i #(readers [V p si vi]) c n_a))))
  | ResponderSentMsg2 srv k_bs a c n_b ->
    let tag = str_to_bytes #i "r_sent_m2" in
    let srv_bytes = str_to_bytes #i srv in
    let a_bytes = str_to_bytes #i a in
    LC.can_flow_transitive i (LC.get_label MSG.oyrs_key_usages c) public (readers [V p i vi]);
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) srv_bytes (concat #i #(readers [V p si vi]) k_bs (concat #i #(readers [V p si vi]) a_bytes (concat #i #(readers [V p si vi]) c n_b))))
  | AuthServerSentMsg3 a b c n_a n_b k_ab ->
  let tag = str_to_bytes #i "srv_sent_m3" in
  let a_bytes = str_to_bytes #i a in
  let b_bytes = str_to_bytes #i b in
  LC.can_flow_transitive i (LC.get_label MSG.oyrs_key_usages c) public (readers [V p si vi]);
  LC.can_flow_transitive i (LC.get_label MSG.oyrs_key_usages n_a) (readers [P p]) (readers [V p si vi]);
  LC.can_flow_transitive i (LC.get_label MSG.oyrs_key_usages n_b) (readers [P p]) (readers [V p si vi]);
  concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) a_bytes (concat #i #(readers [V p si vi]) b_bytes (concat #i #(readers [V p si vi]) c (concat #i #(readers [V p si vi]) n_a (concat #i #(readers [V p si vi]) n_b k_ab)))))
  | ResponderSentMsg4 srv a k_ab ->
    let tag = str_to_bytes #i "r_sent_m4" in
    let srv_bytes = str_to_bytes #i srv in
    let a_bytes = str_to_bytes #i a in
    LC.can_flow_transitive i (LC.get_label MSG.oyrs_key_usages k_ab) (readers [P p]) (readers [V p si vi]);
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) srv_bytes (concat #i #(readers [V p si vi]) a_bytes k_ab))
  | InitiatorRecvedMsg4 srv b k_ab ->
    let tag = str_to_bytes #i "i_rcvd_m4" in
    let srv_bytes = str_to_bytes #i srv in
    let b_bytes = str_to_bytes #i b in
    LC.can_flow_transitive i (LC.get_label MSG.oyrs_key_usages k_ab) (readers [P p]) (readers [V p si vi]);
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) srv_bytes (concat #i #(readers [V p si vi]) b_bytes k_ab))
