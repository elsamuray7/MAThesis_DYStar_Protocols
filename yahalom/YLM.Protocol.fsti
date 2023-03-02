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
open SecurityLemmas


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

val initiator_send_msg_1:
  initiator:principal ->
  kas_idx:nat ->
  responder:principal ->
  LCrypto (msg_idx:timestamp * sess_idx:nat) (pki ylm_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 (mi, si) t1 ->
    mi < trace_len t1 /\ trace_len t0 < trace_len t1))

val responder_send_msg_2:
  responder:principal ->
  kbs_idx:nat ->
  msg_idx:timestamp ->
  LCrypto (msg_idx:timestamp * sess_idx:nat) (pki ylm_preds)
  (requires (fun t0 -> msg_idx < trace_len t0))
  (ensures (fun t0 (mi, si) t1 ->
    mi < trace_len t1 /\ trace_len t0 < trace_len t1))

val server_send_msg_3:
  server:principal ->
  msg_idx:timestamp ->
  LCrypto (msg_idx:timestamp * sess_idx:nat) (pki ylm_preds)
  (requires (fun t0 -> msg_idx < trace_len t0))
  (ensures (fun t0 (mi, si) t1 ->
    mi < trace_len t1 /\ trace_len t0 < trace_len t1))

val initiator_send_msg_4:
  initiator:principal ->
  kas_idx:nat ->
  msg_idx:timestamp ->
  sess_idx:nat ->
  LCrypto (msg_idx:timestamp) (pki ylm_preds)
  (requires (fun t0 -> msg_idx < trace_len t0))
  (ensures (fun t0 mi t1 ->
    mi < trace_len t1 /\ trace_len t0 < trace_len t1))

val responder_recv_msg_4:
  responder:principal ->
  kbs_idx:nat ->
  msg_idx:timestamp ->
  sess_idx:nat ->
  LCrypto unit (pki ylm_preds)
  (requires (fun t0 -> msg_idx < trace_len t0))
  (ensures (fun t0 _ t1 -> trace_len t0 < trace_len t1))
