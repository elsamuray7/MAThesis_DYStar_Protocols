module OYRS.Attacker


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledRuntimeAPI

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
  | _ -> ()
