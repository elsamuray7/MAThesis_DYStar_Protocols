module OYRS.Messages


module LC = LabeledCryptoAPI


let valid_message i m =
  match m with
  | Msg1 c a b ev_a -> LC.is_msg oyrs_global_usage i c public
  | Msg2 c a b ev_a ev_b -> LC.is_msg oyrs_global_usage i c public
  | Msg3 c ev_a ev_b -> LC.is_msg oyrs_global_usage i c public
  | Msg4 c ev_a -> LC.is_msg oyrs_global_usage i c public

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
