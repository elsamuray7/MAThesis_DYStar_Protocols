module OYRS.Attacker


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledRuntimeAPI
open SecurityLemmas

module M = OYRS.Messages
module S = OYRS.Sessions
module L = LabeledPKI
module A = AttackerAPI


/// Interception of message 1 attack:
/// The attacker intercepts the first message initiator -> responder and removes
/// the principals names from the message. The attacker then sends the resulting
/// message back to the initiator, who thinks it came from the responder and interprets
/// the concatenation of the conversation ID and the principals names as the secret
/// conversation key, which the attacker is able to derive by himself.
let attacker_intercept_msg_1 (bob alice:principal) (msg1_idx:nat) :
  Crypto (timestamp * bytes)
         (requires (fun t0 -> msg1_idx < trace_len t0))
         (ensures (fun t0 r t1 ->
         match r with
         | Error _ -> t0 == t1
         | Success (n, b) ->
           A.attacker_modifies_trace t0 t1 /\
           trace_len t1 = trace_len t0 + 1 /\
           later_than (trace_len t1) (trace_len t0) /\
           n = trace_len t0 /\
           A.attacker_knows_at n b))
= // receive and parse first message
  let (|t_m1,ser_msg1|) = A.receive_i msg1_idx bob in

  match
    A.split ser_msg1 `bind` (fun (tag_bytes, rest) ->
    A.pub_bytes_to_string tag_bytes `bind` (fun tag ->
    match tag with
    | "msg1" ->
      A.split rest `bind` (fun (c, rest) ->
      A.split rest `bind` (fun (a_bytes, rest) ->
      A.split rest `bind` (fun (b_bytes, ev_a) ->
      Success (c,a_bytes,b_bytes,ev_a))))
    | t -> Error ("attacker_intercept_m1: wrong message: " ^ t ^ "\n")
    ))
  with
  | Success (c,a_bytes,b_bytes,ev_a) ->
    // derive the conversation key
    let now = global_timestamp () in
    let c = A.pub_bytes_later t_m1 now c in
    let a_bytes = A.pub_bytes_later t_m1 now a_bytes in
    let b_bytes = A.pub_bytes_later t_m1 now b_bytes in
    let conv_key = A.concat c (A.concat a_bytes b_bytes) in

    // create and send malicious "fourth" message
    let msg4_tag = A.pub_bytes_later 0 now (A.string_to_pub_bytes "msg4") in
    let ev_a = A.pub_bytes_later t_m1 now ev_a in
    let ser_msg4 = A.concat msg4_tag (A.concat c ev_a) in

    let send_mal_m4_idx = A.send #now bob alice ser_msg4 in

    (send_mal_m4_idx, conv_key)
  | Error e -> error e

/// Interception of message 2 attack:
/// The attacker intercepts the second message responder -> server and removes
/// the principals names from the message. The attacker then sends the resulting
/// message back to the responder, who thinks it came from the server and interprets
/// the concatenation of the conversation ID and the principals names as the secret
/// conversation key, which the attacker is able to derive by himself.
let attacker_intercept_msg_2 (srv bob:principal) (msg2_idx:nat) :
  Crypto (timestamp * bytes)
         (requires (fun t0 -> msg2_idx < trace_len t0))
         (ensures (fun t0 r t1 ->
         match r with
         | Error _ -> t0 == t1
         | Success (n, b) ->
           A.attacker_modifies_trace t0 t1 /\
           trace_len t1 = trace_len t0 + 1 /\
           later_than (trace_len t1) (trace_len t0) /\
           n = trace_len t0 /\
           A.attacker_knows_at n b))
= // receive and parse second message
  let (|t_m2,ser_msg2|) = A.receive_i msg2_idx srv in

  match
    A.split ser_msg2 `bind` (fun (tag_bytes, rest) ->
    A.pub_bytes_to_string tag_bytes `bind` (fun tag ->
    match tag with
    | "msg2" ->
      A.split rest `bind` (fun (c, rest) ->
      A.split rest `bind` (fun (a_bytes, rest) ->
      A.split rest `bind` (fun (b_bytes, rest) ->
      A.split rest `bind` (fun (ev_a, ev_b) ->
      Success (c,a_bytes,b_bytes,ev_a,ev_b)))))
    | t -> Error ("attacker_intercept_m2: wrong message: " ^ t ^ "\n")
    ))
  with
  | Success (c,a_bytes,b_bytes,ev_a,ev_b) ->
    // derive the conversation key
    let now = global_timestamp () in
    let c = A.pub_bytes_later t_m2 now c in
    let a_bytes = A.pub_bytes_later t_m2 now a_bytes in
    let b_bytes = A.pub_bytes_later t_m2 now b_bytes in
    let conv_key = A.concat c (A.concat a_bytes b_bytes) in

    // create and send malicious third message
    let msg3_tag = A.pub_bytes_later 0 now (A.string_to_pub_bytes "msg3") in
    (* ev_a and ev_b will be interpreted as (nonce, key) where the key is the
    concatenation (c, a, b) in reality. c, a and b are all public. Thus, the
    attacker is in posession of the conversation key that is supposed to be
    secret. *)
    let ev_a = A.pub_bytes_later t_m2 now ev_a in
    let ev_b = A.pub_bytes_later t_m2 now ev_b in
    let ser_msg3 = A.concat msg3_tag (A.concat c (A.concat ev_a ev_b)) in

    let send_mal_m3_idx = A.send #now srv bob ser_msg3 in

    (send_mal_m3_idx, conv_key)
  | Error e -> error e

val query_secret_key: idx_state:nat -> idx_corrupt:nat -> idx_query:nat ->
    p:principal -> si:nat -> vi:nat ->
    LCrypto (A.pub_bytes idx_query) (L.pki S.oyrs_preds)
    (requires (fun t0 -> idx_state < idx_query /\ idx_corrupt < idx_query /\ idx_query <= trace_len t0 /\ was_corrupted_at idx_corrupt p si vi))
    (ensures (fun t0 _ t1 -> t1 == t0))

let query_secret_key idx_state idx_corrupt idx_query p si vi =
  let ser_st = A.query_state_i idx_state idx_corrupt idx_query p si vi in
  match
    A.split ser_st `bind` (fun (tag_bytes, rest) ->
    A.pub_bytes_to_string tag_bytes `bind` (fun lpki_tag ->
    match lpki_tag with
    | "APP" ->
      A.split rest `bind` (fun (tag_bytes, rest) ->
      A.pub_bytes_to_string tag_bytes `bind` (fun oyrs_tag ->
      match oyrs_tag with
      | "r_init" ->
        A.split rest `bind` (fun (srv_bytes, k_es) ->
        Success k_es)
      | "r_sent_m2" ->
        A.split rest `bind` (fun (srv_bytes, rest) ->
        A.split rest `bind` (fun (k_es, _) ->
        Success k_es))
      | t -> Error ("query_secret_key: wrong oyrs session state tag: " ^ t ^ "\n")
      ))
    | t -> Error ("query_secret_key: wrong lpki session state tag: " ^ t ^ "\n")
    ))
  with Success k -> k | Error e -> error e

let attacker_send_mal_msg_2 (#i:nat) (eve srv:principal) (msg1_idx:nat)
  (k_es:A.pub_bytes i) :
  Crypto (timestamp * g_trace)
         (requires (fun t0 -> i <= trace_len t0 /\ msg1_idx < trace_len t0))
         (ensures (fun t0 r t1 ->
         match r with
         | Error _ -> (t0 == t1 \/
           (A.attacker_modifies_trace t0 t1 /\
           later_than (trace_len t1) (trace_len t0)))
         | Success (n, t01) ->
           trace_len t1 = trace_len t0 + 3 /\
           later_than (trace_len t1) (trace_len t0) /\
           n = trace_len t1 - 1 /\
           A.attacker_modifies_trace t0 t01 /\
           A.attacker_modifies_trace t01 t1))
= // receive and parse first message
  let (|t_m1,ser_msg1|) = A.receive_i msg1_idx eve in

  match
    A.split ser_msg1 `bind` (fun (tag_bytes, rest) ->
    A.pub_bytes_to_string tag_bytes `bind` (fun tag ->
    match tag with
    | "msg1" ->
      A.split rest `bind` (fun (c, rest) ->
      A.split rest `bind` (fun (a_bytes, rest) ->
      A.split rest `bind` (fun (b_bytes, ev_a) ->
      Success (c,a_bytes,b_bytes,ev_a))))
    | t -> Error ("attacker_send_mal_m2: wrong message: " ^ t ^ "\n")
    ))
  with
  | Success (c,a_bytes,b_bytes,c_ev_a) ->
    // generate "responder" nonce
    let (|now,n_e|) = A.pub_rand_gen (nonce_usage "nonce_attacker") in
    let intermediate_trace = get () in


    // create and send malicious second message. Muhahah
    let c = A.pub_bytes_later t_m1 now c in
    let a_bytes = A.pub_bytes_later t_m1 now a_bytes in
    let b_bytes = A.pub_bytes_later t_m1 now b_bytes in
    let e_bytes = A.pub_bytes_later 0 now (A.string_to_pub_bytes eve) in
    let c_ev_a = A.pub_bytes_later t_m1 now c_ev_a in

    let ev2 = A.concat n_e (A.concat c (A.concat a_bytes b_bytes)) in
    let k_es = A.pub_bytes_later i now k_es in
    let iv = A.pub_bytes_later 0 now (A.string_to_pub_bytes "iv") in
    let ad = A.pub_bytes_later 0 now (A.string_to_pub_bytes "ev_r") in
    let c_ev2 = A.aead_enc #now k_es iv ev2 ad in

    let msg2_tag = A.pub_bytes_later 0 now (A.string_to_pub_bytes "msg2") in
    let ser_msg2 = A.concat msg2_tag (A.concat c (A.concat a_bytes (A.concat e_bytes (A.concat c_ev_a c_ev2)))) in

    let send_mal_m2_idx = A.send #now eve srv ser_msg2 in

    (send_mal_m2_idx, intermediate_trace)
  | Error e -> error e

let attacker_send_msg_4 (#i:nat) (eve bob alice:principal) (msg3_idx:nat)
  (k_es:A.pub_bytes i) :
  Crypto (timestamp * bytes)
         (requires (fun t0 -> i < trace_len t0 /\ msg3_idx < trace_len t0))
         (ensures (fun t0 r t1 ->
         match r with
         | Error _ -> t0 == t1
         | Success (n, b) ->
           A.attacker_modifies_trace t0 t1 /\
           trace_len t1 = trace_len t0 + 1 /\
           later_than (trace_len t1) (trace_len t0) /\
           n = trace_len t0 /\
           A.attacker_knows_at n b))
= // receive and parse third message
  let (|t_m3,ser_msg3|) = A.receive_i msg3_idx eve in

  match
    A.split ser_msg3 `bind` (fun (tag_bytes, rest) ->
    A.pub_bytes_to_string tag_bytes `bind` (fun tag ->
    match tag with
    | "msg3" ->
      A.split rest `bind` (fun (c, rest) ->
      A.split rest `bind` (fun (ev_a, ev_e) ->
      Success (c,ev_a,ev_e)))
    | t -> Error ("attacker_send_m4: wrong message: " ^ t ^ "\n")
    ))
  with
  | Success (c,c_ev_a,c_ev_e) -> (
    // decrypt part "intended" for attacker and extract conversation key
    let now = global_timestamp () in
    let c_ev_e = A.pub_bytes_later t_m3 now c_ev_e in
    let k_es = A.pub_bytes_later i now k_es in
    let iv = A.pub_bytes_later 0 now (A.string_to_pub_bytes "iv") in
    let ad = A.pub_bytes_later 0 now (A.string_to_pub_bytes "ev_r") in
    match
      A.aead_dec #now k_es iv c_ev_e ad `bind` (fun ev_e ->
      A.split ev_e `bind` (fun (_, k_ab) -> Success k_ab))
    with
    | Success k_ab -> (
      //create and send fourth message
      let c = A.pub_bytes_later t_m3 now c in
      let c_ev_a = A.pub_bytes_later t_m3 now c_ev_a in

      let msg4_tag = A.pub_bytes_later 0 now (A.string_to_pub_bytes "msg4") in
      let ser_msg4 = A.concat msg4_tag (A.concat c c_ev_a) in

      let send_m4_idx = A.send #now bob alice ser_msg4 in

      (send_m4_idx, k_ab)
    )
    | Error e -> error e
  )
  | Error e -> error e

/// The instantiation of this lemma requires that the attacker knows `conv_key`.
/// Its implementation will throw an error if the conversation key is "incorrect".
val attacker_knows_conv_key_stored_in_initiator_or_responder_state:
  p:principal ->
  si:nat ->
  conv_key:bytes ->
  LCrypto unit (L.pki S.oyrs_preds)
  (requires (fun t0 -> A.attacker_knows_at (trace_len t0) conv_key))
  (ensures (fun t0 _ t1 -> True))

let attacker_knows_conv_key_stored_in_initiator_or_responder_state
  p
  si
  conv_key
=
  let now = global_timestamp () in
  let (|_,ser_st|) = L.get_session #(S.oyrs_preds) #now p si in
  match S.parse_session_st ser_st with
  | Success (S.ResponderSentMsg4 srv a k_ab) ->
    if k_ab = conv_key then () else error "attacker could not derive conversation key\n"
  | Success (S.InitiatorRecvedMsg4 srv b k_ab) ->
    if k_ab = conv_key then () else error "attacker could not derive conversation key\n"
  | _ -> error "not a final principal state\n"

val initiator_believes_talking_to_responder:
  i:principal ->
  si:nat ->
  r:principal ->
  LCrypto unit (L.pki S.oyrs_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 _ t1 -> True))

let initiator_believes_talking_to_responder
  i
  si
  r
= let now = global_timestamp () in
  let (|_,ser_st|) = L.get_session #(S.oyrs_preds) #now i si in
  match S.parse_session_st ser_st with
  | Success (S.InitiatorRecvedMsg4 srv b k_ab) ->
    if b = r then () else error "initiator does not believe to talk to responder\n"
  | _ -> error "wrong state\n"

/// This function can be used to check whether initiator and responder talk to
/// each other at runtime
val initiator_and_responder_talk_to_each_other:
  initiator:principal ->
  responder:principal ->
  i_sess_idx:nat ->
  r_sess_idx:nat ->
  LCrypto unit (L.pki S.oyrs_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 _ t1 -> True))

let initiator_and_responder_talk_to_each_other
  initiator
  responder
  i_sess_idx
  r_sess_idx
=
  let now = global_timestamp () in
  let (|i_vers_idx,i_sess|) = L.get_session #(S.oyrs_preds) #now initiator i_sess_idx in
  let (|r_vers_idx,r_sess|) = L.get_session #(S.oyrs_preds) #now responder r_sess_idx in
  match OYRS.Sessions.parse_session_st i_sess with
  | Success (S.InitiatorRecvedMsg4 srv b k_ab) -> (
    match OYRS.Sessions.parse_session_st r_sess with
    | Success (S.ResponderSentMsg4 srv' a k_ab') -> (
      if a <> initiator then error "responder does not believe to talk to initiator\n"
      else if b <> responder then error "initiator does not believe to talk to responder\n"
      else if k_ab <> k_ab' then error "initiator and responder have different keys\n"
      else ()
    )
    | _ -> error "wrong initiator final session\n"
  )
  | _ -> error "wrong responder final session\n"
