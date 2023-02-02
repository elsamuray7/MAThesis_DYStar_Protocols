module DS.Protocol


/// Clock measuring relative trace growth within a Denning-Sacco protocol session
/// from a specific timestamp
val clock:Type0

/// Get the trace growth value of a clock
val clock_getval: clock:clock -> nat
