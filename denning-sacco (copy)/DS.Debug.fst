module DS.Debug


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open SecurityLemmas
open DS.Sessions
open DS.Protocol


val benign_attacker:
  unit ->
  LCrypto unit (pki ds_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

#set-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let benign_attacker () =
  let a:principal = "alice" in
  let b:principal = "bob" in
  let srv:principal = "server" in

  let now = global_timestamp () in
  let sigk_a_idx = gen_private_key #ds_preds #now a SIG "DS.sig_key" in
  let now = global_timestamp () in
  let sk_b_idx = gen_private_key #ds_preds #now b PKE "DS.pke_key" in
  let now = global_timestamp () in
  let sigk_srv_idx = gen_private_key #ds_preds #now srv SIG "DS.sig_key" in

  let now = global_timestamp () in
  let pk_a_srv_idx = install_public_key #ds_preds #now a srv SIG "DS.sig_key" in
  let now = global_timestamp () in
  let pk_b_srv_idx = install_public_key #ds_preds #now b srv PKE "DS.pke_key" in
  let now = global_timestamp () in
  let verk_srv_a_idx = install_public_key #ds_preds #now srv a SIG "DS.sig_key" in
  let now = global_timestamp () in
  let verk_srv_b_idx = install_public_key #ds_preds #now srv b SIG "DS.sig_key" in

  let (msg1_idx, a_sess_idx) = initiator_send_msg_1 a b srv in
  let (msg2_idx, srv_sess_idx, c_sm2) = server_send_msg_2 srv msg1_idx in
  let (msg3_idx, c_sm3) = initiator_send_msg_3 c_sm2 a msg2_idx a_sess_idx in
  let (b_sess_idx, c_end) = responder_recv_msg_3 c_sm3 b srv msg3_idx in
  ()

let benign () : LCrypto unit (pki ds_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get () in
  let x = benign_attacker () in
  print_trace ()

let main =
  IO.print_string "======================\n";
  IO.print_string "Denning-Sacco         \n";
  IO.print_string "======================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker:\n";
  assume(valid_trace (pki ds_preds) t0);
  let r,t1 = (reify (benign ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Denning-Sacco protocol.\n");
  IO.print_string "Finished Benign Attacker:\n"
