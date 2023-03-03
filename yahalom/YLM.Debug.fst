module YLM.Debug


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open SecurityLemmas
open YLM.Sessions
open YLM.Protocol


val benign_attacker:
  unit ->
  LCrypto unit (pki ylm_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

#set-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let benign_attacker () =
  let a:principal = "alice" in
  let b:principal = "bob" in
  let srv:principal = "server" in

  let ((|t_kas,k_as|), kas_idx) = new_lt_key_session a srv in
  let ((|t_kbs,k_bs|), kbs_idx) = new_lt_key_session b srv in
  install_lt_key_at_auth_server #t_kas srv a k_as;
  install_lt_key_at_auth_server #t_kbs srv b k_bs;

  let (msg1_idx, a_sess_idx) = initiator_send_msg_1 a kas_idx b in
  let (msg2_idx, b_sess_idx) = responder_send_msg_2 b kbs_idx msg1_idx in
  let (msg3_idx, srv_sess_idx) = server_send_msg_3 srv msg2_idx in
  let msg4_idx = initiator_send_msg_4 a kas_idx msg3_idx a_sess_idx in
  responder_recv_msg_4 b kbs_idx msg4_idx b_sess_idx;
  ()

let benign () : LCrypto unit (pki ylm_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get () in
  let x = benign_attacker () in
  print_trace ()

let main =
  IO.print_string "======================\n";
  IO.print_string "Yahalom               \n";
  IO.print_string "======================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker:\n";
  assume(valid_trace (pki ylm_preds) t0);
  let r,t1 = (reify (benign ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Yahalom protocol.\n");
  IO.print_string "Finished Benign Attacker:\n"
