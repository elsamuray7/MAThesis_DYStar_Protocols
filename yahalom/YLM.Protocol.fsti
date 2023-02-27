module YLM.Protocol


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open YLM.Messages
open YLM.Sessions
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI


val new_lt_key_session:
  p:principal ->
  server:principal ->
  LCrypto ((i:timestamp & k_ps:lt_key i p server) * sess_idx:nat) (pki ylm_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 ((|i,k_ps|), si) t1 ->
    i == trace_len t0 /\ trace_len t1 == trace_len t0 + 2))

val install_lt_key_at_auth_server:
  #i:nat ->
  server:principal ->
  p:principal ->
  k_ps:lt_key i p server ->
  LCrypto unit (pki ylm_preds)
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 _ t1 -> trace_len t1 == trace_len t0 + 1))
