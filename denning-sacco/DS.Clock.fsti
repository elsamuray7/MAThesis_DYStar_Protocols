module DS.Clock


open SecrecyLabels


/// Clock measuring number of sends and receives in a specific Denning-Sacco
/// protocol session after a specific timestamp
val clock:Type0

/// Get the value of the clocks counter
val clock_get: clock:clock -> nat

/// Tests whether 'base_cnt' is less than or equal to the value of the counter of 'cmp'.
/// Outputs an error if the timestamp does not match with the clocks timestamp.
val clock_lte: ts:timestamp -> base_cnt:nat -> cmp:clock -> result bool
