module DS.Clock


open CryptoEffect
open GlobalRuntimeLib
open SecrecyLabels


/// Clock measuring number of sends and receives in a specific Denning-Sacco
/// protocol session after a specific timestamp
val clock:Type0

/// Get the value of the clocks counter
val clock_get: clock:clock -> nat

/// Outputs a new clock with the current timestamp and a fresh counter
val clock_new: unit -> Crypto clock
  (requires (fun t0 -> True))
  (ensures (fun t0 r t1 ->
    match r with
    | Success clock -> t1 == t0 /\ clock_get clock == 0
    | _ -> False
  ))

/// Tests whether 'base_cnt' is less than or equal to the value of the counter of 'cmp'.
/// Outputs an error if the timestamp does not match with the clocks timestamp.
val clock_lte: ts:timestamp -> base_cnt:nat -> cmp:clock -> r:(result bool)
  {
    match r with
    | Success true -> clock_get cmp <= base_cnt
    | _ -> True
  }
