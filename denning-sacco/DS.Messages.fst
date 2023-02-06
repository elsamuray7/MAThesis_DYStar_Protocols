module DS.Messages


let serialize_encsigval i esv l =
  match esv with
  | SigCertP p pk_p t ->
    let tag = LC.string_to_bytes #ds_global_usage #i "cert_p" in
    let p_bytes = LC.string_to_bytes #ds_global_usage #i p in
    let t_bytes = LC.nat_to_bytes #ds_global_usage #i 0 t in
    LC.concat #ds_global_usage #i #l tag (LC.concat #ds_global_usage #i #l p_bytes (LC.concat #ds_global_usage #i #l pk_p t_bytes))
  | EncSigCommKey ck t ->
    let tag = LC.string_to_bytes #ds_global_usage #i "comm_key" in
    let t_bytes = LC.nat_to_bytes #ds_global_usage #i 0 t in
    LC.concat #ds_global_usage #i #l tag (LC.concat #ds_global_usage #i #l ck t_bytes)

let parse_encsigval #i #l sesv =
  LC.split #ds_global_usage #i #l sesv `bind` (fun (tag_bytes, rest) ->
  LC.bytes_to_string #ds_global_usage #i tag_bytes `bind` (fun tag ->
  match tag with
  | "cert_p" ->
    LC.split #ds_global_usage #i #l rest `bind` (fun (p_bytes, rest) ->
    LC.split #ds_global_usage #i #l rest `bind` (fun (pk_p, t_bytes) ->
    LC.bytes_to_string #ds_global_usage #i p_bytes `bind` (fun p ->
    LC.bytes_to_nat #ds_global_usage #i t_bytes `bind` (fun t ->
    Success (SigCertP p pk_p t)))))
  | "comm_key" ->
    LC.split #ds_global_usage #i #l rest `bind` (fun (ck, t_bytes) ->
    LC.bytes_to_nat #ds_global_usage #i t_bytes `bind` (fun t ->
    Success (EncSigCommKey ck t)))
  | t -> Error ("[parse_encsigval] invalid tag: " ^ t)
  ))

let parse_serialize_encsigval_lemma i esv l = ()


let serialize_msg i m =
  match m with
  | Msg1 a b ->
    let tag = LC.string_to_bytes #ds_global_usage #i "msg1" in
    let a_bytes = LC.string_to_bytes #ds_global_usage #i a in
    let b_bytes = LC.string_to_bytes #ds_global_usage #i b in
    LC.concat #ds_global_usage #i #public tag (LC.concat #ds_global_usage #i #public a_bytes b_bytes)
  | Msg2 cert_a cert_b ->
    let tag = LC.string_to_bytes #ds_global_usage #i "msg2" in
    LC.concat #ds_global_usage #i #public tag (LC.concat #ds_global_usage #i #public cert_a cert_b)
  | Msg3 cert_a cert_b esv_ck ->
    let tag = LC.string_to_bytes #ds_global_usage #i "msg3" in
    LC.concat #ds_global_usage #i #public tag (LC.concat #ds_global_usage #i #public cert_a (LC.concat #ds_global_usage #i #public cert_b esv_ck))

let parse_msg #i sm =
  LC.split #ds_global_usage #i #public sm `bind` (fun (tag_bytes, rest) ->
  LC.bytes_to_string #ds_global_usage #i tag_bytes `bind` (fun tag ->
  match tag with
  | "msg1" ->
    LC.split #ds_global_usage #i #public rest `bind` (fun (a_bytes, b_bytes) ->
    LC.bytes_to_string #ds_global_usage #i a_bytes `bind` (fun a ->
    LC.bytes_to_string #ds_global_usage #i b_bytes `bind` (fun b ->
    Success (Msg1 a b))))
  | "msg2" ->
    LC.split #ds_global_usage #i #public rest `bind` (fun (cert_a, cert_b) ->
    Success (Msg2 cert_a cert_b))
  | "msg3" ->
    LC.split #ds_global_usage #i #public rest `bind` (fun (cert_a, rest) ->
    LC.split #ds_global_usage #i #public rest `bind` (fun (cert_b, esv_ck) ->
    Success (Msg3 cert_a cert_b esv_ck)))
  | t -> Error ("[parse_msg] invalid tag: " ^ t)
  ))

let parse_serialize_msg_lemma i m = ()
