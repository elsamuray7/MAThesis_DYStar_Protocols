module OYRS.Debug


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open ORYS.Sessions
open ORYS.Protocol


val benign_attacker:
  unit ->
  LCrypto unit (pki nsl_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

#set-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let benign_attacker () =
  ()

let benign () : LCrypto unit (pki nsl_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get() in
  let x = benign_attacker () in
  print_trace ()

let main =
  IO.print_string "======================\n";
  IO.print_string "Otway-Rees            \n";
  IO.print_string "======================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker:\n";
  assume(valid_trace (pki nsl_preds) t0);
  let r,t1 = (reify (benign ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Otway-Rees protocol.\n");
  IO.print_string "Finished Benign Attacker:\n"
