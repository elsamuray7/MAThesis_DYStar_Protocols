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

/// Key secrecy on auth server side
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

/// Key secrecy on initiator side
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

/// Key secrecy on responder side
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

/// Initiator authentication to responder.
/// If all principals are honest then there is a matching 'fwd key'
/// event that occured on the initiator side for each 'recv key'
/// event on the responder side.
val initiator_authentication: i:nat ->
  LCrypto unit (pki ylm_preds)
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 _ t1 -> forall a b srv n_b k_ab.
    did_event_occur_at i b (event_recv_key a b srv n_b k_ab)
    ==> (exists n_a. did_event_occur_before i a (event_fwd_key a b srv n_a n_b k_ab)
    \/ corrupt_id i (P a) \/ corrupt_id i (P b) \/ corrupt_id i (P srv))))

/// Responder authentication to initiator.
/// If all principals are honest then there is a matching 'req key'
/// event that occured on the responder side for each 'fwd key'
/// event on the initiator side.
val responder_authentication: i:nat ->
  LCrypto unit (pki ylm_preds)
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 _ t1 -> forall a b srv n_a n_b k_ab.
    did_event_occur_at i a (event_fwd_key a b srv n_a n_b k_ab)
    ==> (did_event_occur_before i b (event_req_key a b srv n_a n_b)
    \/ corrupt_id i (P a) \/ corrupt_id i (P b) \/ corrupt_id i (P srv))))
