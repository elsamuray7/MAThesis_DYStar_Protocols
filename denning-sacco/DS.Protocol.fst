module DS.Protocol


open SecrecyLabels


(* Internal type implementing the public type 'clock' *)
let clock_ = (nat * timestamp)

(* Outputs a new clock starting to count from 0 from given timestamp *)
let clock_new (ts:timestamp) : clock_ = (0,ts)

(* Increases the trace growth value of a clock by 'd' *)
let clock_incval (clock:clock_) (d:nat) : clock_ =
  let (curval,ts) = clock in (curval + d,ts)

(* Assign internal to public type *)
let clock = clock_

let clock_getval clock =
  let (curval,_) = clock in curval
