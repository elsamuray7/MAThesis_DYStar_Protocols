module DS.Messages


open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib

module LC = LabeledCryptoAPI


let ds_key_usages : LC.key_usages = LC.default_key_usages

let can_pke_encrypt (i:nat) s pk m = True
let can_aead_encrypt i s k m ad = True
let can_sign i s k m = True
let can_mac i s k m = True

let ds_usage_preds : LC.usage_preds = {
  LC.can_pke_encrypt = can_pke_encrypt;
  LC.can_aead_encrypt =  can_aead_encrypt;
  LC.can_sign = can_sign;
  LC.can_mac = can_mac
}

let ds_global_usage : LC.global_usage = {
  LC.key_usages = ds_key_usages;
  LC.usage_preds = ds_usage_preds;
}

let msg i l = LC.msg ds_global_usage i l
let is_msg i b l = LC.is_msg ds_global_usage i b l


/// Format of encrypted/signed message parts
noeq type encsigval =
  | SigCertP: p:principal -> pk_p:bytes -> t:timestamp -> encsigval
  | EncSigCommKey: ck:bytes -> t:timestamp -> encsigval

let valid_encsigval (i:nat) (esv:encsigval) (l:label) =
  match esv with
  | SigCertP p pk_p t -> is_msg i pk_p l
  | EncSigCommKey ck t -> is_msg i ck l

val serialize_encsigval: i:nat -> esv:encsigval -> l:label{valid_encsigval i esv l} -> sesv:(msg i l)
val parse_encsigval: #i:nat -> #l:label -> sesv:(msg i l) -> r:(result encsigval)
  {
    match r with
    | Success esv -> valid_encsigval i esv l
    | _ -> True
  }

val parse_serialize_encsigval_lemma: i:nat -> esv:encsigval -> l:label ->
  Lemma (requires (valid_encsigval i esv l))
        (ensures (parse_encsigval (serialize_encsigval i esv l) == Success esv))
        [SMTPat (parse_encsigval (serialize_encsigval i esv l))]


noeq type message (i:nat) =
  | Msg1: a:principal -> b:principal -> message i
  | Msg2: cert_a:msg i public -> cert_b:msg i public -> message i
  | Msg3: cert_a:msg i public -> cert_b:msg i public -> esv_ck:msg i public -> message i

val serialize_msg: i:nat -> m:(message i) -> msg i public
val parse_msg: #i:nat -> sm:(msg i public) -> r:(result (message i))

val parse_serialize_msg_lemma: i:nat -> m:(message i) ->
  Lemma (parse_msg (serialize_msg i m) == Success m)
