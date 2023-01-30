module OYRS.SecurityProps


open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI

open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib

open AttackerAPI

open OYRS.Messages
open OYRS.Sessions

open SecurityLemmas


/// Ensures that the supposedly honest principals involved in the protocol run and the
/// conversation key generated by the auth server for these principals are stored in
/// the auth server state
val principals_and_conv_key_stored_in_auth_server_state:
  (server:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (server_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (responder:principal) ->
  (conv_key:bytes) ->
  Type0

/// Ensures that responder, server and conversation key are stored in the initiator state
val responder_and_server_and_conv_key_stored_in_initiator_state:
  (initiator:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (init_state:state_vec) ->
  (state_session_idx:nat) ->
  (responder:principal) ->
  (server:principal) ->
  (conv_key:bytes) ->
  Type0

/// Ensures that initiator, server and conversation key are stored in the responder state
val initiator_and_server_and_conv_key_stored_in_responder_state:
  (responder:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (resp_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (server:principal) ->
  (conv_key:bytes) ->
  Type0

/// Ensures secrecy of the generated conversation key for honest principals.
/// Note: This does not include general secrecy of the conversation key stored
/// in the states of the initiator and responder, respectively.
val conv_key_stored_in_auth_server_state_is_secret:
  (server:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (server_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (responder:principal) ->
  (conv_key:bytes) ->
  LCrypto unit (pki oyrs_preds)
  (requires (fun in_tr ->
    // Stuff stored in state
    principals_and_conv_key_stored_in_auth_server_state server set_state_idx vv server_state state_session_idx initiator responder conv_key /\
    // State was set before
    set_state_idx < trace_len in_tr
  ))
  (ensures (fun in_tr _ out_tr ->
    in_tr == out_tr /\
    (
      is_unknown_to_attacker_at (trace_len in_tr) conv_key \/
      (
        corrupt_id (trace_len in_tr) (P server) \/
        corrupt_id (trace_len in_tr) (P initiator) \/
        corrupt_id (trace_len in_tr) (P responder)
      )
    )
  ))

/// Ensures secrecy of the conversation key stored in the initiator state
val conv_key_stored_in_initiator_state_is_secret:
  (initiator:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (init_state:state_vec) ->
  (state_session_idx:nat) ->
  (responder:principal) ->
  (server:principal) ->
  (conv_key:bytes) ->
  LCrypto unit (pki oyrs_preds)
  (requires (fun in_tr ->
    // Stuff stored in state
    responder_and_server_and_conv_key_stored_in_initiator_state initiator set_state_idx vv init_state state_session_idx responder server conv_key /\
    // State was set before
    set_state_idx < trace_len in_tr
  ))
  (ensures (fun in_tr _ out_tr ->
    in_tr == out_tr /\
    (
      is_unknown_to_attacker_at (trace_len in_tr) conv_key \/
      (
        corrupt_id (trace_len in_tr) (P server) \/
        corrupt_id (trace_len in_tr) (P initiator) \/
        corrupt_id (trace_len in_tr) (P responder)
      )
    )
  ))

/// Ensures secrecy of the conversation key stored in the responder state
val conv_key_stored_in_responder_state_is_secret:
  (responder:principal) ->
  (set_state_idx:nat) ->
  (vv:version_vec) ->
  (resp_state:state_vec) ->
  (state_session_idx:nat) ->
  (initiator:principal) ->
  (server:principal) ->
  (conv_key:bytes) ->
  LCrypto unit (pki oyrs_preds)
  (requires (fun in_tr ->
    // Stuff stored in state
    initiator_and_server_and_conv_key_stored_in_responder_state responder set_state_idx vv resp_state state_session_idx initiator server conv_key /\
    // State was set before
    set_state_idx < trace_len in_tr
  ))
  (ensures (fun in_tr _ out_tr ->
    in_tr == out_tr /\
    (
      is_unknown_to_attacker_at (trace_len in_tr) conv_key \/
      (
        corrupt_id (trace_len in_tr) (P server) \/
        corrupt_id (trace_len in_tr) (P initiator) \/
        corrupt_id (trace_len in_tr) (P responder)
      )
    )
  ))

val initiator_authentication: i:nat ->
  LCrypto unit (pki oyrs_preds)
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 _ t1 -> forall c a b srv k_ab.
  did_event_occur_at i b (event_forward_key c a b srv k_ab)
  ==> ((exists c n_a. did_event_occur_before i a (event_initiate c a b srv n_a)) \/ corrupt_id i (P a) \/ corrupt_id i (P b) \/ corrupt_id i (P srv))))

val responder_authentication: i:nat ->
  LCrypto unit (pki oyrs_preds)
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 _ t1 -> forall c a b srv k_ab.
  did_event_occur_at i a (event_recv_key c a b srv k_ab)
  ==> ((exists c n_b. did_event_occur_before i b (event_request_key c a b srv n_b)) \/ corrupt_id i (P a) \/ corrupt_id i (P b) \/ corrupt_id i (P srv))))
