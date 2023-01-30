module OYRS.Messages


open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib

module LC = LabeledCryptoAPI


let _ser_encval = (tag:string & bytes)

/// Format of encrypted message parts
noeq type encval =
  | EncMsg1: c:bytes -> a:string -> b:string -> n_a:bytes -> encval
  | EncMsg2: c:bytes -> a:string -> b:string -> n_b:bytes -> encval
  | EncMsg3_I: n_a:bytes -> b:principal -> k_ab:bytes -> encval
  | EncMsg3_R: n_b:bytes -> a:principal -> k_ab:bytes -> encval

let _parse_encval (_sev:_ser_encval) : (r:result encval) =
  match _sev with
  | (|"ev1",sev|) -> (
    split sev `bind` (fun r2 ->
    let (c, rest) = r2 in
    split rest `bind` (fun r3 ->
    let (a_bytes, rest) = r3 in
    split rest `bind` (fun r4 ->
    let (b_bytes, n_a) = r4 in
    bytes_to_string a_bytes `bind` (fun a ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (EncMsg1 c a b n_a)
    )))))
  )
  | (|"ev2",sev|) -> (
    split sev `bind` (fun r2 ->
    let (c, rest) = r2 in
    split rest `bind` (fun r3 ->
    let (a_bytes, rest) = r3 in
    split rest `bind` (fun r4 ->
    let (b_bytes, n_b) = r4 in
    bytes_to_string a_bytes `bind` (fun a ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (EncMsg2 c a b n_b)
    )))))
  )
  | (|"ev3_i",sev|) -> (
    split sev `bind` (fun r2 ->
    let (n_a, rest) = r2 in
    split rest `bind` (fun (b_bytes, k_ab) ->
    bytes_to_string b_bytes `bind` (fun b ->
    Success (EncMsg3_I n_a b k_ab)
    )))
  )
  | (|"ev3_r",sev|) -> (
    split sev `bind` (fun r2 ->
    let (n_b, rest) = r2 in
    split rest `bind` (fun (a_bytes, k_ab) ->
    bytes_to_string a_bytes `bind` (fun a ->
    Success (EncMsg3_R n_b a k_ab)
    )))
  )
  | (|t,_|) -> Error ("invalid tag: " ^ t)


let event_initiate (c:bytes) (a b srv:principal) (n_a:bytes) : event =
  ("initiate",[c;(string_to_bytes a);(string_to_bytes b);(string_to_bytes srv);n_a])
let event_request_key (c:bytes) (a b srv:principal) (n_b:bytes) : event =
  ("req_key",[c;(string_to_bytes a);(string_to_bytes b);(string_to_bytes srv);n_b])
let event_send_key (c:bytes) (a b srv:principal) (n_a n_b k_ab:bytes) : event =
  ("send_key",[c;(string_to_bytes a);(string_to_bytes b);(string_to_bytes srv);n_a;n_b;k_ab])
let event_forward_key (c:bytes) (a b srv:principal) (n_b k_ab:bytes) : event =
  ("fwd_key",[c;(string_to_bytes a);(string_to_bytes b);(string_to_bytes srv);n_b;k_ab])
let event_recv_key (c:bytes) (a b srv:principal) (n_a k_ab:bytes) : event =
  ("recv_key",[c;(string_to_bytes a);(string_to_bytes b);(string_to_bytes srv);n_a;k_ab])


let oyrs_key_usages : LC.key_usages = LC.default_key_usages

let can_pke_encrypt (i:nat) s pk m = True
let can_aead_encrypt i s k ev ad =
  exists p srv. LC.get_label oyrs_key_usages k == readers [P p; P srv] /\
  (match _parse_encval ev with
  | Success (EncMsg1 c a b n_a) ->
    did_event_occur_before i a (event_initiate c a b srv n_a)
  | Success (EncMsg2 c a b n_b) ->
    did_event_occur_before i b (event_request_key c a b srv n_b)
  | Success (EncMsg3_I n_a b k_ab) ->
    was_rand_generated_before i k_ab (readers [P srv; P p; P b]) (aead_usage "sk_i_r") /\
    (exists c n_b. did_event_occur_before i srv (event_send_key c p b srv n_a n_b k_ab))
  | Success (EncMsg3_R n_b a k_ab) ->
    was_rand_generated_before i k_ab (readers [P srv; P a; P p]) (aead_usage "sk_i_r") /\
    (exists c n_a. did_event_occur_before i srv (event_send_key c a p srv n_a n_b k_ab))
  | _ -> False)
let oyrs_aead_pred i s k b ad =
  forall (t:string{bytes_to_string ad = Success t}). can_aead_encrypt i s k (|t,b|) ad
let can_sign i s k m = True
let can_mac i s k m = True

let oyrs_usage_preds : LC.usage_preds = {
  LC.can_pke_encrypt = can_pke_encrypt;
  LC.can_aead_encrypt = oyrs_aead_pred;
  LC.can_sign = can_sign;
  LC.can_mac = can_mac
}

let oyrs_global_usage : LC.global_usage = {
  LC.key_usages = oyrs_key_usages;
  LC.usage_preds = oyrs_usage_preds;
}

let msg i l = LC.msg oyrs_global_usage i l
let is_msg i b l = LC.is_msg oyrs_global_usage i b l


let valid_encval (i:nat) (ev:encval) (l:label) =
  match ev with
  | EncMsg1 c a b n_a -> is_msg i n_a l /\ is_msg i c l
  | EncMsg2 c a b n_b -> is_msg i n_b l /\ is_msg i c l
  | EncMsg3_I n_a b k_ab -> is_msg i n_a l /\ is_msg i k_ab l
  | EncMsg3_R n_b a k_ab -> is_msg i n_b l /\ is_msg i k_ab l

(* Serialized and encrypted encvals with tags *)
let is_ser_encval i (_sev:_ser_encval) l = let (|t,b|) = _sev in (is_msg i b l)
let ser_encval i l = _sev:_ser_encval{is_ser_encval i _sev l}
let enc_encval i = (tag:string & msg i public)

val serialize_encval: i:nat -> ev:encval -> l:label{valid_encval i ev l} -> sev:(ser_encval i l)
  {
    let (|tag,_|) = sev in
    match (tag, ev) with
    | ("ev1", EncMsg1 _ _ _ _)
    | ("ev2", EncMsg2 _ _ _ _)
    | ("ev3_i", EncMsg3_I _ _ _)
    | ("ev3_r", EncMsg3_R _ _ _) -> True
    | _ -> False
  }
val parse_encval: #i:nat -> #l:label -> sev:(ser_encval i l) -> r:(result encval)
  {
    match r with
    | Success ev -> valid_encval i ev l
    | Error _ -> True
  }

val parse_encval_lemma: #i:nat -> #l:label -> sev:(ser_encval i l) ->
  Lemma (parse_encval sev == _parse_encval sev)

val parse_serialize_encval_lemma: i:nat -> ev:encval -> l:label ->
  Lemma (requires (valid_encval i ev l))
        (ensures (parse_encval (serialize_encval i ev l) == Success ev /\
                  _parse_encval (serialize_encval i ev l) == Success ev))
        [SMTPat (parse_encval (serialize_encval i ev l))]

val parsed_encval_is_valid_lemma: #i:nat -> #l:label -> sev:(ser_encval i l) ->
  Lemma (
          match parse_encval sev with
          | Success (EncMsg1 c a b n_a) -> valid_encval i (EncMsg1 c a b n_a) l
          | Success (EncMsg2 c a b n_b) -> valid_encval i (EncMsg2 c a b n_b) l
          | Success (EncMsg3_I n_a b k_ab) -> valid_encval i (EncMsg3_I n_a b k_ab) l
          | Success (EncMsg3_R n_b a k_ab) -> valid_encval i (EncMsg3_R n_b a k_ab) l
          | _ -> True
        )
        [SMTPat (parse_encval sev)]

val can_aead_encrypt_encval_lemma: i:timestamp -> t:string -> l:label -> s:string -> k:bytes -> b:bytes{is_ser_encval i (|t,b|) l} -> ad:bytes{bytes_to_string ad = Success t} ->
  Lemma (exists j. forall (t':string{bytes_to_string ad = Success t'}). (later_than i j /\ can_aead_encrypt j s k (|t',b|) ad) ==> can_aead_encrypt j s k (|t,b|) ad)


noeq type message (i:nat) =
  | Msg1: c:bytes -> a:string -> b:string -> ev_a:enc_encval i -> message i
  | Msg2: c:bytes -> a:string -> b:string -> ev_a:enc_encval i -> ev_b:enc_encval i -> message i
  | Msg3: c:bytes -> ev_a:enc_encval i -> ev_b:enc_encval i -> message i
  | Msg4: c:bytes -> ev_a:enc_encval i -> message i

let valid_message (i:nat) (m:message i) =
  match m with
  | Msg1 c a b (|"ev1",ev_a|) -> is_msg i c public
  | Msg2 c a b (|"ev1",ev_a|) (|"ev2",ev_b|) -> is_msg i c public
  | Msg3 c (|"ev3_i",ev_a|) (|"ev3_r",ev_b|) -> is_msg i c public
  | Msg4 c (|"ev3_i",ev_a|) -> is_msg i c public
  | _ -> False

val serialize_msg: i:nat -> m:(message i){valid_message i m} -> msg i public
val parse_msg: #i:nat -> sm:(msg i public) -> r:(result (message i))
  {
    match r with
    | Success m -> valid_message i m
    | Error _ -> True
  }

val parse_serialize_msg_lemma: i:nat -> m:(message i) ->
  Lemma (requires (valid_message i m))
        (ensures (parse_msg (serialize_msg i m) == Success m))
