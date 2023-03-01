module YLM.Messages


let parse_encval_ sev =
  split sev `bind` (fun (tag_bytes, rest) ->
  bytes_to_string tag_bytes `bind` (fun tag ->
  match tag with
  | "ev2" ->
    split rest `bind` (fun (a_bytes, rest) ->
    split rest `bind` (fun (n_a, n_b) ->
    bytes_to_string a_bytes `bind` (fun a ->
    Success (EncMsg2 a n_a n_b))))
  | "ev3_i" ->
    split rest `bind` (fun (b_bytes, rest) ->
    split rest `bind` (fun (k_ab, rest) ->
    split rest `bind` (fun (n_a, n_b) ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (EncMsg3_I b k_ab n_a n_b)))))
  | "ev3_r" ->
    split rest `bind` (fun (a_bytes, k_ab) ->
    bytes_to_string a_bytes `bind` (fun a ->
    Success (EncMsg3_R a k_ab)))
  | "ev4" ->
    let n_b = rest in
    Success (EncMsg4 n_b)
  | t -> Error ("[parse_encval] invalid tag: " ^ t)
  ))

let serialize_encval i ev l =
  match ev with
  | EncMsg2 a n_a n_b ->
    let tag = str_to_bytes #i "ev2" in
    let a_bytes = str_to_bytes #i a in
    concat #i #l tag (concat #i #l a_bytes (concat #i #l n_a n_b))
  | EncMsg3_I b k_ab n_a n_b ->
    let tag = str_to_bytes #i "ev3_i" in
    let b_bytes = str_to_bytes #i b in
    concat #i #l tag (concat #i #l b_bytes (concat #i #l k_ab (concat #i #l n_a n_b)))
  | EncMsg3_R a k_ab ->
    let tag = str_to_bytes #i "ev3_r" in
    let a_bytes = str_to_bytes #i a in
    concat #i #l tag (concat #i #l a_bytes k_ab)
  | EncMsg4 n_b ->
    let tag = str_to_bytes #i "ev4" in
    concat #i #l tag n_b

let parse_encval #i #l sev =
  split #i #l sev `bind` (fun (tag_bytes, rest) ->
  bytes_to_str #i tag_bytes `bind` (fun tag ->
  match tag with
  | "ev2" ->
    split #i #l rest `bind` (fun (a_bytes, rest) ->
    split #i #l rest `bind` (fun (n_a, n_b) ->
    bytes_to_str #i a_bytes `bind` (fun a ->
    Success (EncMsg2 a n_a n_b))))
  | "ev3_i" ->
    split #i #l rest `bind` (fun (b_bytes, rest) ->
    split #i #l rest `bind` (fun (k_ab, rest) ->
    split #i #l rest `bind` (fun (n_a, n_b) ->
    bytes_to_str #i b_bytes `bind` (fun b ->
    Success (EncMsg3_I b k_ab n_a n_b)))))
  | "ev3_r" ->
    split #i #l rest `bind` (fun (a_bytes, k_ab) ->
    bytes_to_str #i a_bytes `bind` (fun a ->
    Success (EncMsg3_R a k_ab)))
  | "ev4" ->
    let n_b = rest in
    Success (EncMsg4 n_b)
  | t -> Error ("[parse_encval] invalid tag: " ^ t)
  ))

let parse_encval_lemma sev = ()

let parse_serialize_encval_lemma i ev l = ()


let serialize_msg i m =
  match m with
  | Msg1 a n_a ->
    let tag = str_to_bytes #i "msg1" in
    let a_bytes = str_to_bytes #i a in
    concat_pub #i tag (concat_pub #i a_bytes n_a)
  | Msg2 b ev_b ->
    let tag = str_to_bytes #i "msg2" in
    let b_bytes = str_to_bytes #i b in
    concat_pub #i tag (concat_pub b_bytes ev_b)
  | Msg3 ev_a ev_b ->
    let tag = str_to_bytes #i "msg3" in
    concat_pub #i tag (concat_pub #i ev_a ev_b)
  | Msg4 ev3_b ev4_b ->
    let tag = str_to_bytes #i "msg4" in
    concat_pub #i tag (concat_pub #i ev3_b ev4_b)

let parse_msg #i sm =
  split #i sm `bind` (fun (tag_bytes, rest) ->
  bytes_to_str #i tag_bytes `bind` (fun tag ->
  match tag with
  | "msg1" ->
    split #i rest `bind` (fun (a_bytes, n_a) ->
    bytes_to_str #i a_bytes `bind` (fun a ->
    Success (Msg1 a n_a)))
  | "msg2" ->
    split #i rest `bind` (fun (b_bytes, ev_b) ->
    bytes_to_str #i b_bytes `bind` (fun b ->
    Success (Msg2 b ev_b)))
  | "msg3" ->
    split #i rest `bind` (fun (ev_a, ev_b) ->
    Success (Msg3 ev_a ev_b))
  | "msg4" ->
    split #i rest `bind` (fun (ev3_b, ev4_b) ->
    Success (Msg4 ev3_b ev4_b))
  | t -> Error ("[parse_msg] invalid tag: " ^ t)
  ))

let parse_serialize_msg_lemma i m = ()
