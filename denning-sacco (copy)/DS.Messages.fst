module DS.Messages


let parse_sigval_ ssv =
  split ssv `bind` (fun (tag_bytes, rest) ->
  bytes_to_string tag_bytes `bind` (fun tag ->
  match tag with
  | "cert_a" ->
    split rest `bind` (fun (a_bytes, rest) ->
    split rest `bind` (fun (pk_a, t_bytes) ->
    bytes_to_string a_bytes `bind` (fun a ->
    bytes_to_nat t_bytes `bind` (fun t ->
    Success (CertA a pk_a t)))))
  | "cert_b" ->
    split rest `bind` (fun (b_bytes, rest) ->
    split rest `bind` (fun (pk_b, t_bytes) ->
    bytes_to_string b_bytes `bind` (fun b ->
    bytes_to_nat t_bytes `bind` (fun t ->
    Success (CertB b pk_b t)))))
  | "comm_key" ->
    split rest `bind` (fun (ck, t_bytes) ->
    bytes_to_nat t_bytes `bind` (fun t ->
    Success (CommKey ck t)))
  | t -> Error ("[parse_encsigval] invalid tag: " ^ t)
  ))

let parse_encval_comm_key_ enc_sig_ck = split enc_sig_ck

let serialize_sigval i sv l =
  match sv with
  | CertA a pk_a t ->
    let tag = str_to_bytes #i "cert_a" in
    let a_bytes = str_to_bytes #i a in
    let t_bytes = nat_to_bytes #i t in
    concat #i #l tag (concat #i #l a_bytes (concat #i #l pk_a t_bytes))
  | CertB b pk_b t ->
    let tag = str_to_bytes #i "cert_b" in
    let b_bytes = str_to_bytes #i b in
    let t_bytes = nat_to_bytes #i t in
    concat #i #l tag (concat #i #l b_bytes (concat #i #l pk_b t_bytes))
  | CommKey ck t ->
    let tag = str_to_bytes #i "comm_key" in
    let t_bytes = nat_to_bytes #i t in
    concat #i #l tag (concat #i #l ck t_bytes)

let parse_sigval #i #l ssv =
  split #i #l ssv `bind` (fun (tag_bytes, rest) ->
  bytes_to_str #i tag_bytes `bind` (fun tag ->
  match tag with
  | "cert_a" ->
    split #i #l rest `bind` (fun (a_bytes, rest) ->
    split #i #l rest `bind` (fun (pk_a, t_bytes) ->
    bytes_to_str #i a_bytes `bind` (fun a ->
    bytes_to_nat #i t_bytes `bind` (fun t ->
    Success (CertA a pk_a t)))))
  | "cert_b" ->
    split #i #l rest `bind` (fun (b_bytes, rest) ->
    split #i #l rest `bind` (fun (pk_b, t_bytes) ->
    bytes_to_str #i b_bytes `bind` (fun b ->
    bytes_to_nat #i t_bytes `bind` (fun t ->
    Success (CertB b pk_b t)))))
  | "comm_key" ->
    split #i #l rest `bind` (fun (ck, t_bytes) ->
    bytes_to_nat #i t_bytes `bind` (fun t ->
    Success (CommKey ck t)))
  | t -> Error ("[parse_encsigval] invalid tag: " ^ t)
  ))

let parse_sigval_lemma ssv = ()

let parse_serialize_sigval_lemma i sv l = ()


let encval_comm_key i ser_ck sig_ck l = concat #i #l ser_ck sig_ck
let parse_encval_comm_key #i #l enc_sig_ck =
  split #i #l enc_sig_ck `bind` (fun (ser_ck, sig_ck) ->
  let ser_ck:bytes = ser_ck in
  let sig_ck:bytes = sig_ck in
  Success (ser_ck, sig_ck))

let parse_encval_lemma #i #l enc_sig_ck = ()
let parse_serialize_encval_lemma #i #l ser_ck sig_ck = ()

let encval_comm_key_publishable_implies_comm_key_publishable i enc_sig_ck =
  LC.splittable_term_publishable_implies_components_publishable_forall ds_global_usage;
  split_is_split_len_prefixed enc_sig_ck;
  match parse_encval_comm_key_ enc_sig_ck with
  | Success (ser_ck, sig_ck) -> (
    assert(is_succ2 (split_len_prefixed 4 enc_sig_ck) ser_ck sig_ck);
    assert(LC.is_publishable ds_global_usage i enc_sig_ck ==> LC.is_publishable ds_global_usage i ser_ck);
    split_is_split_len_prefixed ser_ck;
    match parse_sigval_ ser_ck with
    | Success (CommKey ck t) ->
      let Success (tag_bytes, rest) = split_len_prefixed 4 ser_ck in
      assert(is_succ2 (split_len_prefixed 4 ser_ck) tag_bytes rest);
      assert(LC.is_publishable ds_global_usage i enc_sig_ck ==> LC.is_publishable ds_global_usage i rest);
      split_is_split_len_prefixed rest;
      let Success (ck', t_bytes) = split_len_prefixed 4 rest in
      assert(is_succ2 (split_len_prefixed 4 rest) ck' t_bytes /\ ck' == ck);
      assert(LC.is_publishable ds_global_usage i enc_sig_ck ==> LC.is_publishable ds_global_usage i ck')
    | _ -> ()
  )
  | _ -> ()


let serialize_msg i m =
  match m with
  | Msg1 a b ->
    let tag = str_to_bytes #i "msg1" in
    let a_bytes = str_to_bytes #i a in
    let b_bytes = str_to_bytes #i b in
    concat_pub #i tag (concat_pub #i a_bytes b_bytes)
  | Msg2 cert_a sig_cert_a cert_b sig_cert_b ->
    let tag = str_to_bytes #i "msg2" in
    concat_pub #i tag (concat_pub #i (concat_pub #i cert_a sig_cert_a) (concat_pub #i cert_b sig_cert_b))
  | Msg3 cert_a sig_cert_a cert_b sig_cert_b enc_sig_ck ->
    let tag = str_to_bytes #i "msg3" in
    concat_pub #i tag (concat_pub #i (concat_pub #i cert_a sig_cert_a) (concat_pub #i (concat_pub #i cert_b sig_cert_b) enc_sig_ck))

let parse_msg #i sm =
  split_pub #i sm `bind` (fun (tag_bytes, rest) ->
  bytes_to_str #i tag_bytes `bind` (fun tag ->
  match tag with
  | "msg1" ->
    split_pub #i rest `bind` (fun (a_bytes, b_bytes) ->
    bytes_to_str #i a_bytes `bind` (fun a ->
    bytes_to_str #i b_bytes `bind` (fun b ->
    Success (Msg1 a b))))
  | "msg2" ->
    split_pub #i rest `bind` (fun (concat_cert_a, concat_cert_b) ->
    split_pub #i concat_cert_a `bind` (fun (cert_a, sig_cert_a) ->
    split_pub #i concat_cert_b `bind` (fun (cert_b, sig_cert_b) ->
    Success (Msg2 cert_a sig_cert_a cert_b sig_cert_b))))
  | "msg3" ->
    split_pub #i rest `bind` (fun (concat_cert_a, rest) ->
    split_pub #i rest `bind` (fun (concat_cert_b, enc_sig_ck) ->
    split_pub #i concat_cert_a `bind` (fun (cert_a, sig_cert_a) ->
    split_pub #i concat_cert_b `bind` (fun (cert_b, sig_cert_b) ->
    Success (Msg3 cert_a sig_cert_a cert_b sig_cert_b enc_sig_ck)))))
  | t -> Error ("[parse_msg] invalid tag: " ^ t)
  ))

let parse_serialize_msg_lemma i m = ()
