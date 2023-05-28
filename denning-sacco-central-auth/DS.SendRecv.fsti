module DS.SendRecv


open SecrecyLabels
open GlobalRuntimeLib
open LabeledPKI
open CryptoEffect
open DS.Clock

module M = DS.Messages
module S = DS.Sessions
module LR = LabeledRuntimeAPI
module LC = LabeledCryptoAPI
module A = AttackerAPI


val send: (#i:timestamp) -> (c_in:clock) -> (sender:principal) -> (receiver:principal) ->
         (message:M.msg i public) -> LR.LCrypto (si:timestamp & c_out:clock) (pki S.ds_preds)
    (requires (fun t0 -> i <= trace_len t0))
    (ensures (fun t0 (|si,c_out|) t1 ->
          si == trace_len t0 /\
          trace_len t1 = trace_len t0 + 1 /\
          was_message_sent_at (trace_len t0) sender receiver message /\
          clock_get c_out = (clock_get c_in) + 1))

val receive_i: (index_of_send_event:timestamp) -> (c_in:clock) -> (receiver:principal) ->
    LR.LCrypto (now:timestamp & c_out:clock & sender:principal & M.msg now public) (pki S.ds_preds)
    (requires (fun t0 -> True))
    (ensures (fun t0 (|now,c_out,sender,t|) t1 ->  t0 == t1 /\
          now = trace_len t0 /\
          index_of_send_event < trace_len t0 /\
          (exists sender receiver. was_message_sent_at index_of_send_event sender receiver t) /\
          clock_get c_out = (clock_get c_in) + 1))

val att_send: #i:timestamp -> c_in:clock -> p1:principal -> p2:principal -> a:A.pub_bytes i -> Crypto (si:timestamp & c_out:clock)
                      (requires (fun t0 -> i <= trace_len t0))
                      (ensures (fun t0 r t1 ->
                        match r with
                        | Error _ -> t0 == t1
                        | Success (|n,c_out|) ->
                          A.attacker_modifies_trace t0 t1 /\
                          trace_len t1 = trace_len t0 + 1 /\
                          later_than (trace_len t1) (trace_len t0) /\
                          n = trace_len t0 /\
                          A.was_published_at (trace_len t0) a /\
                          clock_get c_out = (clock_get c_in) + 1))

val att_receive_i: i:timestamp -> c_in:clock -> p2:principal -> Crypto (j:timestamp & c_out:clock & A.pub_bytes j)
                      (requires (fun t0 -> i < trace_len t0))
                      (ensures (fun t0 r t1 ->
                        t0 == t1 /\
                        (match r with
                         | Error _ -> True
                         | Success (|j,c_out,m|) ->
                           trace_len t0 = j /\ A.was_published_at i m /\
                           (exists p1 p2. was_message_sent_at i p1 p2 m /\
                           clock_get c_out = (clock_get c_in) + 1))))
