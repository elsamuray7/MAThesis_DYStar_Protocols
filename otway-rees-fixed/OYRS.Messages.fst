module OYRS.Messages


module LC = LabeledCryptoAPI


let serialize_encval i ev l =
  match ev with
  | EncMsg1 c a b n_a ->
    let a_bytes = LC.string_to_bytes #oyrs_global_usage #i a in
    let b_bytes = LC.string_to_bytes #oyrs_global_usage #i b in
    (|"ev1",(LC.concat #oyrs_global_usage #i #l c (LC.concat #oyrs_global_usage #i #l a_bytes (LC.concat #oyrs_global_usage #i #l b_bytes n_a)))|)
  | EncMsg2 c a b n_b ->
    let a_bytes = LC.string_to_bytes #oyrs_global_usage #i a in
    let b_bytes = LC.string_to_bytes #oyrs_global_usage #i b in
    (|"ev2",(LC.concat #oyrs_global_usage #i #l c (LC.concat #oyrs_global_usage #i #l a_bytes (LC.concat #oyrs_global_usage #i #l b_bytes n_b)))|)
  | EncMsg3_I n_a b k_ab ->
    let b_bytes = LC.string_to_bytes #oyrs_global_usage #i b in
    (|"ev3_i",(LC.concat #oyrs_global_usage #i #l n_a (LC.concat #oyrs_global_usage #i #l b_bytes k_ab))|)
  | EncMsg3_R n_b a k_ab ->
    let a_bytes = LC.string_to_bytes #oyrs_global_usage #i a in
    (|"ev3_r",(LC.concat #oyrs_global_usage #i #l n_b (LC.concat #oyrs_global_usage #i #l a_bytes k_ab))|)

let parse_encval #i #l (sev:ser_encval i l) =
  match sev with
  | (|"ev1",sev|) -> (
    LC.split #oyrs_global_usage #i #l sev `bind` (fun r2 ->
    let (c, rest) = r2 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r3 ->
    let (a_bytes, rest) = r3 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r4 ->
    let (b_bytes, n_a) = r4 in
    LC.bytes_to_string #oyrs_global_usage #i a_bytes `bind` (fun a ->
    LC.bytes_to_string #oyrs_global_usage #i b_bytes `bind` (fun b ->
    Success (EncMsg1 c a b n_a)
    )))))
  )
  | (|"ev2",sev|) -> (
    LC.split #oyrs_global_usage #i #l sev `bind` (fun r2 ->
    let (c, rest) = r2 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r3 ->
    let (a_bytes, rest) = r3 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun r4 ->
    let (b_bytes, n_b) = r4 in
    LC.bytes_to_string #oyrs_global_usage #i a_bytes `bind` (fun a ->
    LC.bytes_to_string #oyrs_global_usage #i b_bytes `bind` (fun b ->
    Success (EncMsg2 c a b n_b)
    )))))
  )
  | (|"ev3_i",sev|) -> (
    LC.split #oyrs_global_usage #i #l sev `bind` (fun r2 ->
    let (n_a, rest) = r2 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun (b_bytes, k_ab) ->
    LC.bytes_to_string #oyrs_global_usage #i b_bytes `bind` (fun b ->
    Success (EncMsg3_I n_a b k_ab)
    )))
  )
  | (|"ev3_r",sev|) -> (
    LC.split #oyrs_global_usage #i #l sev `bind` (fun r2 ->
    let (n_b, rest) = r2 in
    LC.split #oyrs_global_usage #i #l rest `bind` (fun (a_bytes, k_ab) ->
    LC.bytes_to_string #oyrs_global_usage #i a_bytes `bind` (fun a ->
    Success (EncMsg3_R n_b a k_ab)
    )))
  )
  | (|t,_|) -> Error ("invalid tag: " ^ t)

let parse_serialize_encval_lemma i ev l = ()

let parsed_encval_is_valid_lemma #i #l sev = ()

let can_aead_encrypt_encval_lemma i t l s k b ad =
  assert(forall (t':string{bytes_to_string ad = Success t'}). t' = t);
  assert(forall (t':string{bytes_to_string ad = Success t'}). (|t',b|) = (|t,b|));
  assert(exists j. forall (t':string{bytes_to_string ad = Success t'}). can_aead_encrypt j s k (|t',b|) ad ==> can_aead_encrypt j s k (|t,b|) ad)


let serialize_msg i m =
  match m with
  | Msg1 c a b (|_,ev_a|) ->
    let tag = (LC.string_to_bytes #oyrs_global_usage #i "msg1") in
    let a_bytes = (LC.string_to_bytes #oyrs_global_usage #i a) in
    let b_bytes = (LC.string_to_bytes #oyrs_global_usage #i b) in
    LC.concat #oyrs_global_usage #i #public tag (LC.concat #oyrs_global_usage #i #public c (LC.concat #oyrs_global_usage #i #public a_bytes (LC.concat #oyrs_global_usage #i #public b_bytes ev_a)))
  | Msg2 c a b (|_,ev_a|) (|_,ev_b|) ->
    let tag = (LC.string_to_bytes #oyrs_global_usage #i "msg2") in
    let a_bytes = (LC.string_to_bytes #oyrs_global_usage #i a) in
    let b_bytes = (LC.string_to_bytes #oyrs_global_usage #i b) in
    LC.concat #oyrs_global_usage #i #public tag (LC.concat #oyrs_global_usage #i #public c (LC.concat #oyrs_global_usage #i #public a_bytes (LC.concat #oyrs_global_usage #i #public b_bytes (LC.concat #oyrs_global_usage #i #public ev_a ev_b))))
  | Msg3 c (|_,ev_a|) (|_,ev_b|) ->
    let tag = (LC.string_to_bytes #oyrs_global_usage #i "msg3") in
    LC.concat #oyrs_global_usage #i #public tag (LC.concat #oyrs_global_usage #i #public c (LC.concat #oyrs_global_usage #i #public ev_a ev_b))
  | Msg4 c (|_,ev_a|) ->
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
    Success (Msg1 c a b (|"ev1",ev_a|))
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
    Success (Msg2 c a b (|"ev1",ev_a|) (|"ev2",ev_b|))
    ))))))
  )
  | "msg3" -> (
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r2 ->
    let (c, rest) = r2 in
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r3 ->
    let (ev_a, ev_b) = r3 in
    Success (Msg3 c (|"ev3_i",ev_a|) (|"ev3_r",ev_b|))
    ))
  )
  | "msg4" -> (
    LC.split #oyrs_global_usage #i #public rest `bind` (fun r2 ->
    let (c, ev_a) = r2 in
    Success (Msg4 c (|"ev3_i",ev_a|))
    )
  )
  | t -> Error ("incorrect tag: " ^ t)
  ))

let parse_serialize_msg_lemma i m = ()
