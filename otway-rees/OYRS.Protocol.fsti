module OYRS.Protocol


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open OYRS.Messages
open OYRS.Sessions
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI


val initiator_init:
  initiator:principal ->
  server:principal ->
  responder:principal ->
  LCrypto ((i:timestamp & secret oyrs_global_usage i (readers [P initiator; P server]) (aead_usage "sk_i_srv")) * state_session_idx:nat) (pki oyrs_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 ((|i,s|), si) t1 ->
    i == trace_len t0 /\ trace_len t1 > trace_len t0 /\
    was_rand_generated_at (trace_len t0) s (readers [P initiator; P server]) (aead_usage "sk_i_srv")))

val responder_init:
  responder:principal ->
  server:principal ->
  LCrypto ((i:timestamp & secret oyrs_global_usage i (readers [P responder; P server]) (aead_usage "sk_r_srv")) * state_session_idx:nat) (pki oyrs_preds)
  (requires (fun t0 -> True))
  (ensures (fun t0 ((|i,s|), si) t1 ->
    i == trace_len t0 /\ trace_len t1 > trace_len t0 /\
    was_rand_generated_at (trace_len t0) s (readers [P responder; P server]) (aead_usage "sk_r_srv")))

val install_sk_at_auth_server:
  #i:nat ->
  server:principal ->
  p:principal ->
  sk:(msg oyrs_global_usage i (readers [P p; P server])) ->
  LCrypto unit (pki oyrs_preds)
  (requires fun t0 -> i < trace_len t0)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)

val initiator_send_msg_1:
  initiator:principal ->
  i_sess_idx:nat ->
  LCrypto (message_idx:timestamp) (pki oyrs_preds)
  (requires fun t0 -> True)
  (ensures fun t0 msg_idx t1 -> msg_idx < trace_len t1 /\ (trace_len t0 < trace_len t1))

val responder_send_msg_2:
  responder:principal ->
  message_idx: nat ->
  r_sess_idx:nat ->
  LCrypto (message_idx:nat) (pki oyrs_preds)
  (requires fun t0 ->  message_idx < trace_len t0)
  (ensures fun t0 msg_idx t1 -> msg_idx < trace_len t1 /\ (trace_len t0 < trace_len t1))

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
  (requires fun t0 ->  message_idx < trace_len t0)
  (ensures fun t0 msg_idx t1 -> msg_idx < trace_len t1 /\ (trace_len t0 < trace_len t1))

val initiator_recv_msg_4:
  initiator:principal ->
  sess_idx_init:nat ->
  message_idx:nat ->
  LCrypto unit (pki oyrs_preds)
  (requires fun t0 -> message_idx < trace_len t0)
  (ensures fun t0 _ t1 -> True)
