module DS.Messages


open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib

module LC = LabeledCryptoAPI


(* Events required to proof security properties *)

let event_initiate (a b srv:principal) =
  ("initiate",[string_to_bytes a;string_to_bytes b;string_to_bytes srv])
let event_certify (a b srv:principal) (pk_a pk_b:bytes) (t:timestamp) (clock_cnt:nat) =
  ("certify",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;pk_a;pk_b;nat_to_bytes 0 t;nat_to_bytes 0 clock_cnt])
let event_send_key (a b srv:principal) (pk_a pk_b ck:bytes) (t:timestamp) (clock_cnt:nat) =
  ("send_key",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;pk_a;pk_b;ck;nat_to_bytes 0 t;nat_to_bytes 0 clock_cnt])
let event_accept_key (a b srv:principal) (pk_a pk_b ck:bytes) (t:timestamp) (clock_cnt:nat) =
  ("accept_key",[string_to_bytes a;string_to_bytes b;string_to_bytes srv;pk_a;pk_b;ck;nat_to_bytes 0 t;nat_to_bytes 0 clock_cnt])

(* Expected message receive delays in the Denning-Sacco protocol model *)

/// Initiator side second message receive delay
let recv_msg_2_delay:nat = 2
/// Responder side third message receive delay
let recv_msg_3_delay:nat = recv_msg_2_delay + 2


/// Format of encrypted/signed message parts
noeq type sigval =
  | CertA: a:principal -> pk_a:bytes -> t:timestamp -> sigval
  | CertB: b:principal -> pk_b:bytes -> t:timestamp -> sigval
  | CommKey: ck:bytes -> t:timestamp -> sigval

val parse_sigval_: ssv:bytes -> result sigval


let ds_key_usages : LC.key_usages = LC.default_key_usages

let can_pke_encrypt (i:nat) s pk m = True
let can_aead_encrypt i s k m ad = True
let can_sign i s k ssv =
  exists p. LC.get_signkey_label ds_key_usages k == readers [P p] /\
  (match parse_sigval_ ssv with
  | Success (CertA a pk_a t) ->
    (exists b pk_b. did_event_occur_before i p (event_certify a b p pk_a pk_b t 0))
  | Success (CertB b pk_b t) ->
    (exists a pk_a. did_event_occur_before i p (event_certify a b p pk_a pk_b t 0))
  | Success (CommKey ck t) ->
    exists b. was_rand_generated_before i ck (readers [P p; P b]) (aead_usage "DS.comm_key") /\
    (exists srv pk_a pk_b. did_event_occur_before i p (event_send_key p b srv pk_a pk_b ck t recv_msg_2_delay))
  | _ -> False)
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

(* Denning-Sacco specific aliases *)

let msg i l = LC.msg ds_global_usage i l
let is_msg i b l = LC.is_msg ds_global_usage i b l

let str_to_bytes #i s = LC.string_to_bytes #ds_global_usage #i s
let nat_to_bytes #i n = LC.nat_to_bytes #ds_global_usage #i 0 n
let bytes_to_str #i #l b = LC.bytes_to_string #ds_global_usage #i #l b
let bytes_to_nat #i #l b = LC.bytes_to_nat #ds_global_usage #i #l b
let concat #i #l b1 b2 = LC.concat #ds_global_usage #i #l b1 b2
let concat_pub #i b1 b2 = concat #i #public b1 b2
let split #i #l b = LC.split #ds_global_usage #i #l b
let split_pub #i b = split #i #public b


let valid_sigval (i:nat) (sv:sigval) (l:label) =
  match sv with
  | CertA a pk_a t -> is_msg i pk_a l
  | CertB b pk_b t -> is_msg i pk_b l
  | CommKey ck t -> is_msg i ck l

val serialize_sigval: i:nat -> sv:sigval -> l:label{valid_sigval i sv l} -> ssv:(msg i l)
val parse_sigval: #i:nat -> #l:label -> ssv:(msg i l) -> r:(result sigval)
  {
    match r with
    | Success sv -> valid_sigval i sv l
    | _ -> True
  }

val parse_sigval_lemma: #i:nat -> #l:label -> ssv:(msg i l) ->
  Lemma (parse_sigval ssv == parse_sigval_ ssv)

val parse_serialize_sigval_lemma: i:nat -> sv:sigval -> l:label ->
  Lemma (requires (valid_sigval i sv l))
        (ensures (parse_sigval (serialize_sigval i sv l) == Success sv /\
                  parse_sigval_ (serialize_sigval i sv l) == Success sv))
        [SMTPat (parse_sigval (serialize_sigval i sv l));
         SMTPat (parse_sigval_ (serialize_sigval i sv l))]


/// Create message part to be encrypted, containing the communication key and
/// a corresponding certificate
val encval_comm_key: #i:nat -> #l:label -> ser_ck:msg i l -> sig_ck:msg i l -> enc_sig_ck:msg i l

/// Parse decrypted message part, containing the communication key and
/// a corresponding certificate
val parse_encval_comm_key: #i:nat -> #l:label -> enc_sig_ck:msg i l -> result (ser_ck:msg i l * sig_ck:msg i l)

val parse_serialize_encval_lemma: #i:nat -> #l:label -> ser_ck:msg i l -> sig_ck:msg i l ->
  Lemma (parse_encval_comm_key (encval_comm_key ser_ck sig_ck) == Success (ser_ck, sig_ck))


noeq type message (i:nat) =
  | Msg1: a:principal -> b:principal -> message i
  | Msg2: cert_a:msg i public -> sig_cert_a:msg i public -> cert_b:msg i public -> sig_cert_b:msg i public -> message i
  | Msg3: cert_a:msg i public -> sig_cert_a:msg i public -> cert_b:msg i public -> sig_cert_b:msg i public -> enc_sig_ck:msg i public -> message i

val serialize_msg: i:nat -> m:(message i) -> msg i public
val parse_msg: #i:nat -> sm:(msg i public) -> r:(result (message i))

val parse_serialize_msg_lemma: i:nat -> m:(message i) ->
  Lemma (parse_msg (serialize_msg i m) == Success m)
