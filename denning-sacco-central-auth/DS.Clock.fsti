module DS.Clock


open CryptoEffect
open SecrecyLabels
open LabeledRuntimeAPI

module L = LabeledPKI
module A = AttackerAPI


/// Clock measuring number of sends and receives in a specific Denning-Sacco
/// protocol session after a specific timestamp
val clock:Type0

/// Get the value of the clocks counter
val clock_get: c:clock -> nat

/// Outputs a new clock with the current timestamp and a fresh counter
val clock_new: #pr:preds -> principal ->
  LCrypto (c_new:clock & ts:timestamp) (L.pki pr)
  (requires (fun t0 -> True))
  (ensures (fun t0 (|c_new,ts|) t1 ->
    trace_len t1 == (trace_len t0) + 1  /\
    clock_get c_new == 0 /\
    ts == trace_len t0))

/// Outputs a new clock with the current timestamp and a fresh counter
val att_clock_new: unit ->
  Crypto (c_new:clock & ts:timestamp)
  (requires (fun t0 -> True))
  (ensures (fun t0 r t1 ->
    match r with
    | Success (|c_new,ts|) ->
      A.attacker_modifies_trace t0 t1 /\
      trace_len t1 == (trace_len t0) + 1 /\
      later_than (trace_len t1) (trace_len t0) /\
      clock_get c_new == 0 /\
      ts == trace_len t0
    | Error _ -> t0 == t1
  ))

/// Tests whether 'max_delay' is less than or equal to the value of the counter of 'c'.
/// Outputs an error if the timestamp does not match with the clocks timestamp.
val clock_lte: ts:timestamp -> max_delay:nat -> c:clock -> r:(result bool)
  {
    match r with
    | Success true -> clock_get c <= max_delay
    | _ -> True
  }
