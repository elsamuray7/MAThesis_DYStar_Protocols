module YLM.Messages


open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib

module LC = LabeledCryptoAPI


(* Events required to proof security properties *)

let event_initiate (a b srv:principal) (n_a:bytes) =
  ("initiate",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;n_a])
let event_req_key (a b srv:principal) (n_a n_b:bytes) =
  ("req_key",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;n_a;n_b])
let event_send_key (a b srv:principal) (n_a n_b k_ab:bytes) =
  ("send_key",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;n_a;n_b;k_ab])
let event_recv_key (a b srv:principal) (n_a n_b k_ab:bytes) =
  ("recv_key",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;n_a;n_b;k_ab])
let event_fwd_key (a b srv:principal) (n_b k_ab:bytes) =
  ("recv_key",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;n_b;k_ab])


/// Fromat of encrypted message parts
noeq type encval =
  | EncMsg2: a:principal -> n_a:bytes -> n_b:bytes -> encval
  | EncMsg3_I: b:principal -> k_ab:bytes -> n_a:bytes -> n_b:bytes -> encval
  | EncMsg3_R: a:principal -> k_ab:bytes -> encval
  | EncMsg4: n_b:bytes -> encval

val parse_encval_: sev:bytes -> result encval


let ylm_key_usages : LC.key_usages = LC.default_key_usages

let can_pke_encrypt (i:nat) s pk m = True
let can_aead_encrypt i s k m ad = True
let can_sign i s k m = True
let can_mac i s k m = True

let ylm_usage_preds : LC.usage_preds = {
  LC.can_pke_encrypt = can_pke_encrypt;
  LC.can_aead_encrypt =  can_aead_encrypt;
  LC.can_sign = can_sign;
  LC.can_mac = can_mac
}

let ylm_global_usage : LC.global_usage = {
  LC.key_usages = ylm_key_usages;
  LC.usage_preds = ylm_usage_preds;
}


(* Yahalom specific aliases *)

let msg i l = LC.msg ylm_global_usage i l
let is_msg i b l = LC.is_msg ylm_global_usage i b l

let str_to_bytes #i s = LC.string_to_bytes #ylm_global_usage #i s
let concat #i #l b1 b2 = LC.concat #ylm_global_usage #i #l b1 b2
let concat_pub #i b1 b2 = concat #i #public b1 b2
let bytes_to_str #i #l b = LC.bytes_to_string #ylm_global_usage #i #l b
let split #i #l b = LC.split #ylm_global_usage #i #l b


let valid_encval (i:nat) (ev:encval) (l:label) =
  match ev with
  | EncMsg2 a n_a n_b -> is_msg i n_a l /\ is_msg i n_b l
  | EncMsg3_I b k_ab n_a n_b -> is_msg i k_ab l /\ is_msg i n_a l /\ is_msg i n_b l
  | EncMsg3_R a k_ab -> is_msg i k_ab l
  | EncMsg4 n_b -> is_msg i n_b l

val serialize_encval: i:nat -> ev:encval -> l:label{valid_encval i ev l} -> sev:(msg i l)
val parse_encval: #i:nat -> #l:label -> sev:(msg i l) -> r:(result encval)
  {
    match r with
    | Success ev -> valid_encval i ev l
    | Error _ -> True
  }

val parse_encval_lemma: #i:nat -> #l:label -> sev:(msg i l) ->
  Lemma (parse_encval sev == parse_encval_ sev)

val parse_serialize_encval_lemma: i:nat -> ev:encval -> l:label ->
  Lemma (requires (valid_encval i ev l))
        (ensures (parse_encval (serialize_encval i ev l) == Success ev /\
                  parse_encval_ (serialize_encval i ev l) == Success ev))
        [SMTPat (parse_encval (serialize_encval i ev l));
         SMTPat (parse_encval_ (serialize_encval i ev l))]


noeq type message (i:nat) =
  | Msg1: a:principal -> n_a:bytes -> message i
  | Msg2: b:principal -> ev_b:msg i public -> message i
  | Msg3: ev_a:msg i public -> ev_b:msg i public -> message i
  | Msg4: ev3_b:msg i public -> ev4_b:msg i public -> message i

let valid_message (i:nat) (m:message i) =
  match m with
  | Msg1 a n_a -> is_msg i n_a public
  | _ -> True

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
