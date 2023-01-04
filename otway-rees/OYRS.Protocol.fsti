module OYRS.Protocol


open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open ORYS.Messages
open ORYS.Sessions
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI


val initiator_send_msg_1:
  initiator:principal ->
  responder:principal ->
  LCrypto (state_session_idx:nat * message_idx:nat) (pki oyrs_preds)
  (requires fun t0 -> True)
  (ensures fun t0 (si, msg_idx) t1 -> msg_idx < trace_len t1 /\ (trace_len t0 < trace_len t1))

val responder_send_msg_2:
  responder:principal ->
  message_idx: nat ->
  LCrypto (state_session_idx:nat * message_idx:nat) (pki orys_preds)
  (requires fun t0 ->  message_idx < trace_len t0)
  (ensures fun t0 (si, msg_idx) t1 -> msg_idx < trace_len t1 /\ (trace_len t0 < trace_len t1))

val server_send_msg_3:
  server:principal ->
  message_idx: nat ->
  LCrypto (state_session_idx:nat * message_idx:nat) (pki oyrs_preds)
  (requires fun t0 ->  message_idx < trace_len t0)
  (ensures fun t0 (si, msg_idx) t1 -> msg_idx < trace_len t1 /\ (trace_len t0 < trace_len t1))

val responder_send_msg_4:
  responder:principal ->
  sess_idx_resp:nat ->
  message_idx:nat ->
  LCrypto (message_idx:nat) (pki oyrs_preds)
  (requires fun t0 ->  msg_idx < trace_len t0)
  (ensures fun t0 msg_idx t1 -> msg_idx < trace_len t1 /\ (trace_len t0 < trace_len t1))

val initiator_recv_msg_4:
  initiator:principal ->
  sess_idx_init:nat ->
  message_idx:nat ->
  LCrypto unit (pki oyrs_preds)
  (requires fun t0 -> message_idx < trace_len t0)
  (ensures fun t0 _ t1 -> True)
