module DS.Protocol


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open DS.Messages
open DS.Sessions
open DS.Clock
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI

module SR = DS.SendRecv


val initiator_send_msg_1:
  initiator:principal ->
  responder:principal ->
  server:principal ->
  LCrypto (msg_idx:timestamp * sess_idx:nat) (pki ds_preds)
  (requires fun t0 -> True)
  (ensures fun t0 (mi, si) t1 -> mi < trace_len t1 /\ trace_len t0 < trace_len t1)

val server_send_msg_2:
  server:principal ->
  msg_idx:timestamp ->
  LCrypto (msg_idx:timestamp * sess_idx:nat * c_out:clock) (pki ds_preds)
  (requires fun t0 -> msg_idx < trace_len t0)
  (ensures fun t0 (mi, si, c_out) t1 -> mi < trace_len t1 /\ trace_len t0 < trace_len t1 /\
                                     clock_get c_out = 1)

val initiator_send_msg_3:
  c_in:clock ->
  initiator:principal ->
  msg_idx:timestamp ->
  sess_idx:nat ->
  LCrypto (msg_idx:timestamp * c_out:clock) (pki ds_preds)
  (requires fun t0 -> msg_idx < trace_len t0)
  (ensures fun t0 (mi, c_out) t1 -> mi < trace_len t1 /\ trace_len t0 < trace_len t1 /\
                                 clock_get c_out = (clock_get c_in) + 2)

val responder_recv_msg_3:
  c_in:clock ->
  responder:principal ->
  msg_idx:timestamp ->
  LCrypto (sess_idx:nat * c_out:clock) (pki ds_preds)
  (requires fun t0 -> msg_idx < trace_len t0)
  (ensures fun t0 (si, c_out) t1 -> trace_len t0 < trace_len t1 /\
                                 clock_get c_out = (clock_get c_in + 1))
