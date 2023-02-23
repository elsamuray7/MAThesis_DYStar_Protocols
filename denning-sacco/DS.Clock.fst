module DS.Clock


(* Internal clock type *)
let clock_ = (counter:nat * timestamp)

(* Adds 'd' to the clocks counter *)
let clock_add (clock:clock_) (d:nat) : clock_ =
  let (counter, ts) = clock in (counter + d, ts)


(* Interface implementation *)

(* Assign internal to public type *)
let clock = clock_

let clock_get clock =
  let (counter, _) = clock in counter

let clock_new () = let ts = global_timestamp () in (0, ts)

let clock_lte ts base_cnt cmp =
  let (cnt_cmp, ts_cmp) = cmp in
  if ts_cmp = ts then Success (cnt_cmp <= base_cnt)
  else Error "[clock_lte] Timestamps do not match"
