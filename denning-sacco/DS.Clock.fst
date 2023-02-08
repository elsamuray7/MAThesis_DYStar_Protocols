module DS.Clock


(* Internal clock type *)
let clock_ = (counter:nat * timestamp)

(* Outputs a new clock with given timestamp and counter set to 0 *)
let clock_new (ts:timestamp) : clock_ = (0, ts)

(* Adds 'd' to the clocks counter *)
let clock_add (clock:clock_) (d:nat) : clock_ =
  let (counter, ts) = clock in (counter + d, ts)


(* Interface implementation *)

(* Assign internal to public type *)
let clock = clock_

let clock_get clock =
  let (counter, _) = clock in counter

let clock_lte base other =
  let (cnt_base, ts_base) = base in
  let (cnt_other, ts_other) = other in
  if ts_base = ts_other then Success (cnt_base <= cnt_other)
  else Error "[clock_lte] Clocks are not comparable"
