module DS.Protocol


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open DS.Messages
open DS.Sessions
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI


val intitiator_send_msg_1:
  initiator:principal ->
  server:principal ->
  LCrypto (msg_idx:timestamp * sess_idx:nat) (pki ds_preds)
  (requires fun t0 -> True)
  (ensures fun t0 (mi, si) t1 -> mi < trace_len t1 /\ si < trace_len t1 /\ trace_len t0 < trace_len t1)

val server_send_msg_2:
  server:principal ->
  msg_idx:timestamp ->
  LCrypto (msg_idx:timestamp * sess_idx:nat) (pki ds_preds)
  (requires fun t0 -> msg_idx < trace_len t0)
  (ensures fun t0 (mi, si) t1 -> mi < trace_len t1 /\ si < trace_len t1 /\ trace_len t0 < trace_len t1)

val initiator_send_msg_3:
  initiator:principal ->
  msg_idx:timestamp ->
  sess_idx:nat ->
  LCrypto (msg_idx:timestamp) (pki ds_preds)
  (requires fun t0 -> msg_idx < trace_len t0)
  (ensures fun t0 mi t1 -> mi < trace_len t1 /\ trace_len t0 < trace_len t1)

val responder_recv_msg_3:
  responder:principal ->
  msg_idx:timestamp ->
  LCrypto (msg_idx:timestamp * sess_idx:nat) (pki ds_preds)
  (requires fun t0 -> msg_idx < trace_len t0)
  (ensures fun t0 (mi, si) t1 -> mi < trace_len t1 /\ si < trace_len t1 /\ trace_len t0 < trace_len t1)
