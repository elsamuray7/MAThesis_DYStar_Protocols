module DS.Sessions


let serialize_session_st i p si vi st =
  match st with
  | InitiatorSentMsg1 b srv ->
    let tag = str_to_bytes #i "i_sent_m1" in
    let b_bytes = str_to_bytes #i b in
    let srv_bytes = str_to_bytes #i srv in
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) b_bytes srv_bytes)
  | AuthServerSentMsg2 a b ->
    let tag = str_to_bytes #i "srv_sent_m2" in
    let a_bytes = str_to_bytes #i a in
    let b_bytes = str_to_bytes #i b in
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) a_bytes b_bytes)
  | InitiatorSentMsg3 b ck ->
    let tag = str_to_bytes #i "i_sent_m3" in
    let b_bytes = str_to_bytes #i b in
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) b_bytes ck)
  | ResponderRecvedMsg3 a ck ->
    let tag = str_to_bytes #i "r_rcvd_m3" in
    let a_bytes = str_to_bytes #i a in
    LC.can_flow_transitive i (LC.get_label M.ds_key_usages ck) (readers [P p]) (readers [V p si vi]);
    concat #i #(readers [V p si vi]) tag (concat #i #(readers [V p si vi]) a_bytes ck)

let parse_session_st sst =
  split sst `bind` (fun (tag_bytes, rest) ->
  bytes_to_string tag_bytes `bind` (fun tag ->
  match tag with
  | "i_sent_m1" ->
    split rest `bind` (fun (b_bytes, srv_bytes) ->
    bytes_to_string b_bytes `bind` (fun b ->
    bytes_to_string srv_bytes `bind` (fun srv ->
    Success (InitiatorSentMsg1 b srv))))
  | "srv_sent_m2" ->
    split rest `bind` (fun (a_bytes, b_bytes) ->
    bytes_to_string a_bytes `bind` (fun a ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (AuthServerSentMsg2 a b))))
  | "i_sent_m3" ->
    split rest `bind` (fun (b_bytes, ck) ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (InitiatorSentMsg3 b ck)))
  | "r_rcvd_m3" ->
    split rest `bind` (fun (a_bytes, ck) ->
    bytes_to_string a_bytes `bind` (fun a ->
    Success (ResponderRecvedMsg3 a ck)))
  | t -> Error ("[parse_session_st] invalid tag: " ^ t)
  ))

let parse_serialize_session_st_lemma i p si vi st =
  match st with
  | ResponderRecvedMsg3 a ck ->
    LC.can_flow_transitive i (LC.get_label M.ds_key_usages ck) (readers [P p]) (readers [V p si vi])
  | _ -> ()
