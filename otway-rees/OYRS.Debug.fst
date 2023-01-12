module OYRS.Debug


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open OYRS.Sessions
open OYRS.Protocol


val benign_attacker:
  unit ->
  LCrypto unit (pki oyrs_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

#set-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let benign_attacker () =
  let a:principal = "initiator" in
  let b:principal = "responder" in
  let srv:principal = "server" in

  let ((|t_as,k_as|), a_si) = initiator_init a srv b in
  let ((|t_bs,k_bs|), b_si) = responder_init b srv in
  install_sk_at_auth_server #t_as srv a k_as;
  install_sk_at_auth_server #t_bs srv b k_bs;

  let msg1_idx = initiator_send_msg_1 a a_si in
  let msg2_idx = responder_send_msg_2 b msg1_idx b_si in

  ()

let benign () : LCrypto unit (pki oyrs_preds)
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
  assume(valid_trace (pki oyrs_preds) t0);
  let r,t1 = (reify (benign ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Otway-Rees protocol.\n");
  IO.print_string "Finished Benign Attacker:\n"
