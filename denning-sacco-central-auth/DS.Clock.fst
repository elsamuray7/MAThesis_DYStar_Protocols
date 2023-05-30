module DS.Clock


open GlobalRuntimeLib
open LabeledCryptoAPI


(* Internal clock type *)
let clock_ = (counter:nat * timestamp)

(* Adds 'd' to the clocks counter *)
let clock_add (c:clock_) (d:nat) : clock_ =
  let (counter, ts) = c in (counter + d, ts)


(* Interface implementation *)

(* Assign internal to public type *)
let clock = clock_

let clock_get clock =
  let (counter, _) = clock in counter

let clock_new #pr p =
  let ts = global_timestamp () in
  let _ = L.send #pr #ts p p (nat_to_bytes #pr.global_usage #ts 0 ts) in
  (|(0, ts),ts|)

let att_clock_new () =
  let ts = A.global_timestamp () in
  let _ = A.send #ts "*" "*" (A.pub_bytes_later 0 ts (A.nat_to_pub_bytes 0 ts)) in
  (|(0, ts),ts|)

let clock_lte ts max_delay c =
  let (cnt_c, ts_c) = c in
  if ts_c = ts then Success (cnt_c <= max_delay)
  else Error "[clock_lte] Timestamps do not match"
