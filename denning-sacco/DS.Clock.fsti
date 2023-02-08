module DS.Clock


open SecrecyLabels


/// Clock measuring number of sends and receives in a specific Denning-Sacco
/// protocol session
val clock:Type0

/// Get the value of the clocks counter
val clock_get: clock:clock -> nat

/// Tests whether 'base' is less than or equal to 'other'.
/// Returns an error if the clocks are not comparable.
val clock_lte: base:clock -> other:clock -> result bool
