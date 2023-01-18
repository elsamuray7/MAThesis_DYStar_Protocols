module OYRS.Attacker


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledRuntimeAPI

module S = OYRS.Sessions
module L = LabeledPKI
module A = AttackerAPI


let attacker_intercept_msg_2 (eve srv bob:principal) (msg2_idx:nat) :
  Crypto timestamp
         (requires (fun t0 -> msg2_idx < trace_len t0))
         (ensures (fun t0 n t1 ->
         match n with
         | Error _ -> t0 == t1
         | Success n ->
           A.attacker_modifies_trace t0 t1 /\
           trace_len t1 = trace_len t0 + 1 /\
           later_than (trace_len t1) (trace_len t0) /\
           n = trace_len t0))
= // receive and parse second message
  let (|t_m2,ser_msg2|) = A.receive_i msg2_idx eve in

  match
    A.split ser_msg2 `bind` (fun (tag_bytes, rest) ->
    A.pub_bytes_to_string tag_bytes `bind` (fun tag ->
    match tag with
    | "msg2" ->
      A.split rest `bind` (fun (c, rest) ->
      A.split rest `bind` (fun (_, rest) ->
      A.split rest `bind` (fun (_, rest) ->
      A.split rest `bind` (fun (ev_a, ev_b) ->
      Success (|c,ev_a,ev_b|)))))
    | t -> Error ("attacker_intercept_m2: wrong message: " ^ t)
    ))
  with
  | Success (|c,ev_a,ev_b|) ->
    // create and send malicious third message
    let now = global_timestamp () in
    let msg3_tag = A.pub_bytes_later 0 now (A.string_to_pub_bytes "msg3") in
    let c = A.pub_bytes_later t_m2 now c in
    (* ev_a and ev_b will be interpreted as (nonce, key) where the key is the
    concatenation (c, a, b) in reality. c, a and b are all public. Thus, the
    attacker is in posession of the conversation key that is supposed to be
    secret. *)
    let ev_a = A.pub_bytes_later t_m2 now ev_a in
    let ev_b = A.pub_bytes_later t_m2 now ev_b in
    let ser_msg3 = A.concat msg3_tag (A.concat c (A.concat ev_a ev_b)) in

    A.send #now srv bob ser_msg3
  | Error e -> error e
