module OYRS.Messages


module LC = LabeledCryptoAPI


let valid_encval i ev l =
  match ev with
  | EncMsg1 n_a c a b -> is_msg i n_a l /\ is_msg i c l
  | EncMsg2 n_b c a b -> is_msg i n_b l /\ is_msg i c l
  | EncMsg3_I n_a k_ab -> is_msg i n_a l /\ is_msg i k_ab l
  | EncMsg3_R n_b k_ab -> is_msg i n_b l /\ is_msg i k_ab l

let serialize_encval i ev l =
  match ev with
  | EncMsg1 n_a c a b ->
    let tag = LC.string_to_bytes #oyrs_global_usage #i "ev1" in
    let a_bytes = LC.string_to_bytes #oyrs_global_usage #i a in
    let b_bytes = LC.string_to_bytes #oyrs_global_usage #i b in
    LC.concat #oyrs_global_usage #i #l tag (LC.concat #oyrs_global_usage #i #l n_a (LC.concat #oyrs_global_usage #i #l c (LC.concat #oyrs_global_usage #i #l a_bytes b_bytes)))
  | EncMsg2 n_b c a b ->
    let tag = LC.string_to_bytes #oyrs_global_usage #i "ev2" in
    let a_bytes = LC.string_to_bytes #oyrs_global_usage #i a in
    let b_bytes = LC.string_to_bytes #oyrs_global_usage #i b in
    LC.concat #oyrs_global_usage #i #l tag (LC.concat #oyrs_global_usage #i #l n_b (LC.concat #oyrs_global_usage #i #l c (LC.concat #oyrs_global_usage #i #l a_bytes b_bytes)))
  | EncMsg3_I n_a k_ab ->
    let tag = LC.string_to_bytes #oyrs_global_usage #i "ev3_i" in
    LC.concat #oyrs_global_usage #i #l tag (LC.concat #oyrs_global_usage #i #l n_a k_ab)
  | EncMsg3_R n_b k_ab ->
    let tag = LC.string_to_bytes #oyrs_global_usage #i "ev3_r" in
    LC.concat #oyrs_global_usage #i #l tag (LC.concat #oyrs_global_usage #i #l n_b k_ab)

let parse_encval #i #l (sev:msg i l) =
  LC.split #oyrs_global_usage #i #l sev `bind` (fun r1 ->
  let (tag_bytes, rest) = r1 in
  LC.bytes_to_string #oyrs_global_usage #i tag_bytes `bind` (fun tag ->
  match tag with
  | "ev1" -> (
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r2 ->
    let (n_a, rest) = r2 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r3 ->
    let (c, rest) = r3 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r4 ->
    let (a_bytes, b_bytes) = r4 in
    LC.bytes_to_string #oyrs_global_usage #i a_bytes `bind` (fun a ->
    LC.bytes_to_string #oyrs_global_usage #i b_bytes `bind` (fun b ->
    Success (EncMsg1 n_a c a b)
    )))))
  )
  | "ev2" -> (
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r2 ->
    let (n_b, rest) = r2 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r3 ->
    let (c, rest) = r3 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r4 ->
    let (a_bytes, b_bytes) = r4 in
    LC.bytes_to_string #oyrs_global_usage #i a_bytes `bind` (fun a ->
    LC.bytes_to_string #oyrs_global_usage #i b_bytes `bind` (fun b ->
    Success (EncMsg2 n_b c a b)
    )))))
  )
  | "ev3_i" -> (
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r2 ->
    let (n_a, k_ab) = r2 in
    Success (EncMsg3_I n_a k_ab)
    )
  )
  | "ev3_r" -> (
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r2 ->
    let (n_b, k_ab) = r2 in
    Success (EncMsg3_R n_b k_ab)
    )
  )
  | t -> Error ("invalid tag: " ^ t)
  ))

let parse_serialize_encval_lemma i ev l = ()


let valid_message i m =
  match m with
  | Msg1 c a b ev_a -> is_msg i c public
  | Msg2 c a b ev_a ev_b -> is_msg i c public
  | Msg3 c ev_a ev_b -> is_msg i c public
  | Msg4 c ev_a -> is_msg i c public

let serialize_msg i m =
  match m with
  | Msg1 c a b ev_a ->
    let tag = (LC.string_to_bytes #oyrs_global_usage #i "msg1") in
    let a_bytes = (LC.string_to_bytes #oyrs_global_usage #i a) in
    let b_bytes = (LC.string_to_bytes #oyrs_global_usage #i b) in
    LC.concat #oyrs_global_usage #i #public tag (LC.concat #oyrs_global_usage #i #public c (LC.concat #oyrs_global_usage #i #public a_bytes (LC.concat #oyrs_global_usage #i #public b_bytes ev_a)))
  | Msg2 c a b ev_a ev_b ->
    let tag = (LC.string_to_bytes #oyrs_global_usage #i "msg2") in
    let a_bytes = (LC.string_to_bytes #oyrs_global_usage #i a) in
    let b_bytes = (LC.string_to_bytes #oyrs_global_usage #i b) in
    LC.concat #oyrs_global_usage #i #public tag (LC.concat #oyrs_global_usage #i #public c (LC.concat #oyrs_global_usage #i #public a_bytes (LC.concat #oyrs_global_usage #i #public b_bytes (LC.concat #oyrs_global_usage #i #public ev_a ev_b))))
  | Msg3 c ev_a ev_b ->
    let tag = (LC.string_to_bytes #oyrs_global_usage #i "msg3") in
    LC.concat #oyrs_global_usage #i #public tag (LC.concat #oyrs_global_usage #i #public c (LC.concat #oyrs_global_usage #i #public ev_a ev_b))
  | Msg4 c ev_a ->
    let tag = (LC.string_to_bytes #oyrs_global_usage #i "msg4") in
    LC.concat #oyrs_global_usage #i #public tag (LC.concat #oyrs_global_usage #i #public c ev_a)

let parse_msg #i (sm:msg i public) =
  LC.split #oyrs_global_usage #i #public sm `bind` (fun r1 ->
  let (tag_bytes, rest) = r1 in
  LC.bytes_to_string #oyrs_global_usage #i tag_bytes `bind` (fun tag ->
  match tag with
  | "msg1" -> (
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r2 ->
    let (c, rest) = r2 in
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r3 ->
    let (a_bytes, rest) = r3 in
    LC.bytes_to_string #oyrs_global_usage #i a_bytes `bind` (fun a ->
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r4 ->
    let (b_bytes, ev_a) = r4 in
    LC.bytes_to_string #oyrs_global_usage #i b_bytes `bind` (fun b ->
    Success (Msg1 c a b ev_a)
    )))))
  )
  | "msg2" -> (
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r2 ->
    let (c, rest) = r2 in
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r3 ->
    let (a_bytes, rest) = r3 in
    LC.bytes_to_string #oyrs_global_usage #i a_bytes `bind` (fun a ->
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r4 ->
    let (b_bytes, rest) = r4 in
    LC.bytes_to_string #oyrs_global_usage #i b_bytes `bind` (fun b ->
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r5 ->
    let (ev_a, ev_b) = r5 in
    Success (Msg2 c a b ev_a ev_b)
    ))))))
  )
  | "msg3" -> (
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r2 ->
    let (c, rest) = r2 in
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r3 ->
    let (ev_a, ev_b) = r3 in
    Success (Msg3 c ev_a ev_b)
    ))
  )
  | "msg4" -> (
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r2 ->
    let (c, ev_a) = r2 in
    Success (Msg4 c ev_a)
    )
  )
  | t -> Error ("incorrect tag: " ^ t)
  ))

let parse_serialize_msg_lemma i m = ()
