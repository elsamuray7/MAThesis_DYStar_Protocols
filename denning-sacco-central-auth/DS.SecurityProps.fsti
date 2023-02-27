module DS.SecurityProps


open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI

open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib

open AttackerAPI

open DS.Messages
open DS.Sessions

open SecurityLemmas


val initiator_state_contains_responder_and_comm_key:
  initiator:principal ->
  set_state_idx:nat ->
  vv:version_vec ->
  initiator_state:state_vec ->
  state_session_idx:nat ->
  responder:principal ->
  comm_key:bytes ->
  Type0

val responder_state_contains_initiator_and_comm_key:
  responder:principal ->
  set_state_idx:nat ->
  vv:version_vec ->
  responder_state:state_vec ->
  state_session_idx:nat ->
  initiator:principal ->
  comm_key:bytes ->
  Type0

/// Key secrecy property on the initiator side
val initiator_comm_key_is_secret:
  initiator:principal ->
  set_state_idx:nat ->
  vv:version_vec ->
  initiator_state:state_vec ->
  state_session_idx:nat ->
  responder:principal ->
  comm_key:bytes ->
  LCrypto unit (pki ds_preds)
  (requires (fun t0 ->
    initiator_state_contains_responder_and_comm_key initiator set_state_idx vv initiator_state state_session_idx responder comm_key /\
    set_state_idx < trace_len t0
  ))
  (ensures (fun t0 _ t1 ->
    t0 == t1 /\
    (is_unknown_to_attacker_at (trace_len t0) comm_key \/
    corrupt_id (trace_len t0) (P auth_srv) \/ corrupt_id (trace_len t0) (P initiator) \/ corrupt_id (trace_len t0) (P responder))
  ))

/// Key secrecy property on the responder side
val responder_comm_key_is_secret:
  responder:principal ->
  set_state_idx:nat ->
  vv:version_vec ->
  responder_state:state_vec ->
  state_session_idx:nat ->
  initiator:principal ->
  comm_key:bytes ->
  LCrypto unit (pki ds_preds)
  (requires (fun t0 ->
    responder_state_contains_initiator_and_comm_key responder set_state_idx vv responder_state state_session_idx initiator comm_key /\
    set_state_idx < trace_len t0
  ))
  (ensures (fun t0 _ t1 ->
    t0 == t1 /\
    (is_unknown_to_attacker_at (trace_len t0) comm_key \/
    corrupt_id (trace_len t0) (P auth_srv) \/ corrupt_id (trace_len t0) (P initiator) \/ corrupt_id (trace_len t0) (P responder))
  ))

/// Denning-Sacco claim that their protocol mitigates replays of communication keys against
/// the responder/accepting party.
/// In our model, this property is modeled based on the timestamp and clock counters that
/// occured in the events 'accept key' of the responder and 'certify' of the server.
/// Thus, the property does not hold if the server is corrupted.
val responder_comm_key_is_not_replay: i:nat ->
  LCrypto unit (pki ds_preds)
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 _ t1 -> forall a b pk_a pk_b ck t clock_cnt.
    did_event_occur_at i b (event_accept_key a b pk_a pk_b ck t clock_cnt)
    ==> clock_cnt <= recv_msg_3_delay /\ (did_event_occur_at t auth_srv (event_certify a b pk_a pk_b t 0) \/ corrupt_id i (P auth_srv))))

/// Mutual authentication based on certificates issued by the server.
/// TODO: Is this enough?
val mutual_authentication: i:nat -> j:nat ->
  LCrypto unit (pki ds_preds)
  (requires (fun t0 -> i < trace_len t0 /\ j < trace_len t0 /\ i < j))
  (ensures (fun t0 _ t1 -> forall a b pk_a pk_b ck t clock_cnt_a clock_cnt_b.
    did_event_occur_at i a (event_send_key a b pk_a pk_b ck t clock_cnt_a) /\
    did_event_occur_at j b (event_accept_key a b pk_a pk_b ck t clock_cnt_b)
    ==> t < i /\ did_event_occur_at t auth_srv (event_certify a b pk_a pk_b t 0) \/ corrupt_id i (P auth_srv)))

/// Alternative and "stronger" definition of authentication property for initiator
val initiator_authentication: i:nat ->
  LCrypto unit (pki ds_preds)
  (requires (fun t0 -> i < trace_len t0))
  (ensures (fun t0 _ t1 -> forall a b pk_a pk_b ck t clock_cnt.
    did_event_occur_at i b (event_accept_key a b pk_a pk_b ck t clock_cnt)
    ==> (exists clock_cnt'. clock_cnt' <= recv_msg_2_delay /\ did_event_occur_before i a (event_send_key a b pk_a pk_b ck t clock_cnt') \/ corrupt_id i (P a)) /\
        t < i /\ did_event_occur_at t auth_srv (event_certify a b pk_a pk_b t 0) \/
        corrupt_id i (P auth_srv)))
