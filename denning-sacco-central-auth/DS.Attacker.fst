module DS.Attacker


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledRuntimeAPI
open SecurityLemmas
open DS.Clock
open DS.SendRecv

module M = DS.Messages
module S = DS.Sessions
module L = LabeledPKI
module A = AttackerAPI


val query_secret_key:
    idx_state:nat -> idx_corrupt:nat -> idx_query:nat ->
    p:principal -> s:nat -> v:nat -> 
    LCrypto (A.pub_bytes idx_query) (L.pki S.ds_preds)
    (requires (fun t0 -> idx_state < idx_query /\ idx_corrupt < idx_query /\ idx_query <= trace_len t0 /\ was_corrupted_at idx_corrupt p s v))
    (ensures (fun t0 _ t1 -> t1 == t0))
let query_secret_key idx_state idx_corrupt idx_query p s v =
    let t = A.query_state_i idx_state idx_corrupt idx_query p s v in
    match A.split t with 
    | Success (tag, b) -> // tag == PKI
      (match A.split b with 
      | Success (tag, b) -> b // Due to the string on key-usages in LabeledPKI, we need to split again
      | _ -> b)
    | _ -> error "incorrect tag"

val query_public_key:
    idx_state:nat -> idx_corrupt:nat -> idx_query:nat ->
    p:principal -> s:nat -> v:nat -> 
    LCrypto (A.pub_bytes idx_query) (L.pki S.ds_preds)
    (requires (fun t0 -> idx_state < idx_query /\ idx_corrupt < idx_query /\ idx_query <= trace_len t0 /\ was_corrupted_at idx_corrupt p s v))
    (ensures (fun t0 _ t1 -> t1 == t0))
let query_public_key idx_state idx_corrupt idx_query p s v =
    let t = A.query_state_i idx_state idx_corrupt idx_query p s v in
    match A.split t with 
    | Success (tag, b) -> // tag == PKI
      (match A.split b with 
      // Due to the string on key-usages in LabeledPKI, we need to split again
      | Success (tag, b) -> (match A.split b with 
			   | Success (tag, b) -> b // public key contains peer name
			   | _ -> b) 
      | _ -> b)
    | _ -> error "incorrect tag"

let attacker_issue_fake_cert (#i:timestamp) (eve:principal)
  (sigk_srv pk_a pk_e: A.pub_bytes i) (msg1_idx:timestamp) :
  Crypto (msg2_idx:timestamp & c_out:clock)
  (requires (fun t0 -> msg1_idx < trace_len t0 /\
    later_than (trace_len t0) i))
  (ensures (fun t0 r t1 ->
    match r with
    | Success (|mi,c_out|) ->
      (exists it. A.attacker_modifies_trace t0 it /\
      A.attacker_modifies_trace it t1) /\
      trace_len t1 == (trace_len t0) + 3 /\
      later_than (trace_len t1) (trace_len t0) /\
      mi == (trace_len t1) - 1 /\
      clock_get c_out == 1
    | Error _ -> t0 == t1 \/
      (A.attacker_modifies_trace t0 t1 /\
      later_than (trace_len t1) (trace_len t0)))) =
  // receive and parse first message
  let (|t_m1,ser_msg1|) = A.receive_i msg1_idx M.auth_srv in

  match
    A.split ser_msg1 `bind` (fun (tag_bytes, rest) ->
    A.pub_bytes_to_string tag_bytes `bind` (fun tag ->
    match tag with
    | "msg1" ->
      A.split rest `bind` (fun (a_bytes, b_bytes) ->
      A.pub_bytes_to_string a_bytes `bind` (fun a ->
      Success (a_bytes, a, b_bytes)))
    | t -> Error ("[attacker_issue_fake_cert] wrong message: " ^ t)
    ))
  with
  | Success (a_bytes, a, b_bytes) ->
    // obtain timestamp and create clock
    let t = global_timestamp () in
    let c_new = clock_new () in

    // generate sign nonce
    let (|t_n_sig,n_sig|) = A.pub_rand_gen (nonce_usage "SIG_NONCE") in

    // create legitimate certificate for alice
    let t_bytes = A.pub_bytes_later 0 t_n_sig (A.nat_to_pub_bytes 0 t) in
    let a_bytes = A.pub_bytes_later t_m1 t_n_sig a_bytes in
    let pk_a = A.pub_bytes_later i t_n_sig pk_a in
    let cert_a_tag = A.pub_bytes_later 0 t_n_sig (A.string_to_pub_bytes "cert_a") in
    let ser_cert_a = A.concat cert_a_tag (A.concat a_bytes (A.concat pk_a t_bytes)) in
    let sigk_srv = A.pub_bytes_later i t_n_sig sigk_srv in
    let sig_cert_a = A.sign sigk_srv n_sig ser_cert_a in

    // create fake certificate for bob
    let b_bytes = A.pub_bytes_later t_m1 t_n_sig b_bytes in
    let pk_e = A.pub_bytes_later i t_n_sig pk_e in
    let cert_b_tag = A.pub_bytes_later 0 t_n_sig (A.string_to_pub_bytes "cert_b") in
    let ser_fake_cert_b = A.concat cert_b_tag (A.concat b_bytes (A.concat pk_e t_bytes)) in
    let sig_fake_cert_b = A.sign sigk_srv n_sig ser_fake_cert_b in

    // create and send second message
    let msg2_tag = A.pub_bytes_later 0 t_n_sig (A.string_to_pub_bytes "msg2") in
    let ser_msg2 = A.concat msg2_tag (A.concat sig_cert_a sig_fake_cert_b) in

    att_send #t_n_sig c_new M.auth_srv a ser_msg2
  | Error e -> error e
