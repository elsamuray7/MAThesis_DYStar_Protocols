module YLM.SecurityProps


open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI

open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib

open AttackerAPI

open YLM.Messages
open YLM.Sessions

open SecurityLemmas


val auth_server_state_contains_principals_and_comm_key:
  (server:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (server_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (responder:principal) ->
  (comm_key:bytes) ->
  Type0

val initiator_state_contains_responder_server_and_comm_key:
  (initiator:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (init_state:state_vec) ->
  (state_session_idx:nat) ->
  (responder:principal) ->
  (server:principal) ->
  (comm_key:bytes) ->
  Type0

val responder_state_contains_initiator_server_and_comm_key:
  (responder:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (resp_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (server:principal) ->
  (comm_key:bytes) ->
  Type0

val auth_server_comm_key_is_secret:
  (server:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (server_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (responder:principal) ->
  (comm_key:bytes) ->
  LCrypto unit (pki ylm_preds)
  (requires (fun t0 ->
    auth_server_state_contains_principals_and_comm_key server set_state_idx vv server_state state_session_idx initiator responder comm_key /\
    set_state_idx < trace_len t0
  ))
  (ensures (fun t0 _ t1 ->
    t0 == t1 /\
    (is_unknown_to_attacker_at (trace_len t0) comm_key \/
    corrupt_id (trace_len t0) (P server) \/ corrupt_id (trace_len t0) (P initiator) \/ corrupt_id (trace_len t0) (P responder))
  ))

val initiator_comm_key_is_secret:
  (initiator:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (init_state:state_vec) ->
  (state_session_idx:nat) ->
  (responder:principal) ->
  (server:principal) ->
  (comm_key:bytes) ->
  LCrypto unit (pki ylm_preds)
  (requires (fun t0 ->
    initiator_state_contains_responder_server_and_comm_key initiator set_state_idx vv init_state state_session_idx responder server comm_key /\
    set_state_idx < trace_len t0
  ))
  (ensures (fun t0 _ t1 ->
    t0 == t1 /\
    (is_unknown_to_attacker_at (trace_len t0) comm_key \/
    corrupt_id (trace_len t0) (P server) \/ corrupt_id (trace_len t0) (P initiator) \/ corrupt_id (trace_len t0) (P responder))
  ))

val responder_comm_key_is_secret:
  (responder:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (resp_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (server:principal) ->
  (comm_key:bytes) ->
  LCrypto unit (pki ylm_preds)
  (requires (fun t0 ->
    responder_state_contains_initiator_server_and_comm_key responder set_state_idx vv resp_state state_session_idx initiator server comm_key /\
    set_state_idx < trace_len t0
  ))
  (ensures (fun t0 _ t1 ->
    t0 == t1 /\
    (is_unknown_to_attacker_at (trace_len t0) comm_key \/
    corrupt_id (trace_len t0) (P server) \/ corrupt_id (trace_len t0) (P initiator) \/ corrupt_id (trace_len t0) (P responder))
  ))
