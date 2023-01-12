module OYRS.Messages


open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib

module LC = LabeledCryptoAPI


let oyrs_key_usages : LC.key_usages = LC.default_key_usages

let can_pke_encrypt (i:nat) s pk m = True
let can_aead_encrypt i s k m ad = True
let can_sign i s k m = True
let can_mac i s k m = True

let oyrs_usage_preds : LC.usage_preds = {
  LC.can_pke_encrypt = can_pke_encrypt;
  LC.can_aead_encrypt =  can_aead_encrypt;
  LC.can_sign = can_sign;
  LC.can_mac = can_mac
}

let oyrs_global_usage : LC.global_usage = {
  LC.key_usages = oyrs_key_usages;
  LC.usage_preds = oyrs_usage_preds;
}

let msg i l = LC.msg oyrs_global_usage i l
let is_msg i b l = LC.is_msg oyrs_global_usage i b l


/// Format of encrypted message parts
noeq type encval =
  | EncMsg1: n_a:bytes -> c:bytes -> a:string -> b:string -> encval
  | EncMsg2: n_b:bytes -> c:bytes -> a:string -> b:string -> encval
  | EncMsg3_I: n_a:bytes -> k_ab:bytes -> encval
  | EncMsg3_R: n_b:bytes -> k_ab:bytes -> encval

let valid_encval (i:nat) (ev:encval) (l:label) =
  match ev with
  | EncMsg1 n_a c a b -> is_msg i n_a l /\ is_msg i c l
  | EncMsg2 n_b c a b -> is_msg i n_b l /\ is_msg i c l
  | EncMsg3_I n_a k_ab -> is_msg i n_a l /\ is_msg i k_ab l
  | EncMsg3_R n_b k_ab -> is_msg i n_b l /\ is_msg i k_ab l

val serialize_encval: i:nat -> ev:encval -> l:label{valid_encval i ev l} -> msg i l
val parse_encval: #i:nat -> #l:label -> sev:(msg i l) -> r:(result encval)
  {
    match r with
    | Success ev -> valid_encval i ev l
    | Error _ -> True
  }

val parse_serialize_encval_lemma: i:nat -> ev:encval -> l:label ->
  Lemma (requires (valid_encval i ev l))
        (ensures (parse_encval (serialize_encval i ev l) == Success ev))


noeq type message (i:nat) =
  | Msg1: c:bytes -> a:string -> b:string -> ev_a:msg i public -> message i
  | Msg2: c:bytes -> a:string -> b:string -> ev_a:msg i public -> ev_b:msg i public -> message i
  | Msg3: c:bytes -> ev_a:msg i public -> ev_b:msg i public -> message i
  | Msg4: c:bytes -> ev_a:msg i public -> message i

let valid_message (i:nat) (m:message i) =
  match m with
  | Msg1 c a b ev_a -> is_msg i c public
  | Msg2 c a b ev_a ev_b -> is_msg i c public
  | Msg3 c ev_a ev_b -> is_msg i c public
  | Msg4 c ev_a -> is_msg i c public

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
