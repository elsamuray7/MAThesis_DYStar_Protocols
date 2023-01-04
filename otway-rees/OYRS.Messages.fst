module OYRS.Messages


module LC = LabeledCryptoAPI


let valid_message i (m:message i) =
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
