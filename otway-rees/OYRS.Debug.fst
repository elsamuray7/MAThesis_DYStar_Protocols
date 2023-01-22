module OYRS.Debug


open SecrecyLabels
open CryptoEffect
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open SecurityLemmas
open OYRS.Sessions
open OYRS.Protocol
open OYRS.Attacker


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

  let ((|t_as,us_as,k_as|), a_si) = initiator_init a srv b in
  let ((|t_bs,us_bs,k_bs|), b_si) = responder_init b srv in
  install_sk_at_auth_server #t_as #us_as srv a k_as;
  install_sk_at_auth_server #t_bs #us_bs srv b k_bs;

  let msg1_idx = initiator_send_msg_1 a a_si in
  let msg2_idx = responder_send_msg_2 b msg1_idx b_si in
  let (srv_si, msg3_idx) = server_send_msg_3 srv msg2_idx in
  let msg4_idx = responder_send_msg_4 b msg3_idx b_si in
  initiator_recv_msg_4 a msg4_idx a_si

val intercept_msg_1_attacker:
  unit ->
  LCrypto unit (pki oyrs_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let intercept_msg_1_attacker () =
  let a:principal = "initiator" in
  let b:principal = "responder" in
  let srv:principal = "server" in

  let ((|t_as,us_as,k_as|), a_si) = initiator_init a srv b in
  let ((|t_bs,us_bs,k_bs|), b_si) = responder_init b srv in
  install_sk_at_auth_server #t_as #us_as srv a k_as;
  install_sk_at_auth_server #t_bs #us_bs srv b k_bs;

  let msg1_idx = initiator_send_msg_1 a a_si in
  let (msg4_idx, conv_key) = attacker_intercept_msg_1 b a msg1_idx in
  initiator_recv_msg_4 a msg4_idx a_si;

  // TODO: no mutual authentication either -> proof needed
  attacker_knows_conv_key_stored_in_initiator_or_responder_state a a_si conv_key

val intercept_msg_2_attacker:
  unit ->
  LCrypto unit (pki oyrs_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let intercept_msg_2_attacker () =
  let a:principal = "initiator" in
  let b:principal = "responder" in
  let srv:principal = "server" in

  let ((|t_as,us_as,k_as|), a_si) = initiator_init a srv b in
  let ((|t_bs,us_bs,k_bs|), b_si) = responder_init b srv in
  install_sk_at_auth_server #t_as #us_as srv a k_as;
  install_sk_at_auth_server #t_bs #us_bs srv b k_bs;

  let msg1_idx = initiator_send_msg_1 a a_si in
  let msg2_idx = responder_send_msg_2 b msg1_idx b_si in
  // third message from auth server is discarded
  let (msg3_idx, conv_key) = attacker_intercept_msg_2 srv b msg2_idx in
  let msg4_idx = responder_send_msg_4 b msg3_idx b_si in
  initiator_recv_msg_4 a msg4_idx a_si;

  // TODO: at least we should get mutual authentication here -> proof needed
  attacker_knows_conv_key_stored_in_initiator_or_responder_state a a_si conv_key;
  attacker_knows_conv_key_stored_in_initiator_or_responder_state b b_si conv_key

val impersonate_resp_to_init_attacker:
  unit ->
  LCrypto unit (pki oyrs_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let impersonate_resp_to_init_attacker () =
  let a:principal = "alice" in
  let b:principal = "bob" in
  let srv:principal = "server" in
  let e:principal = "eve" in

  let ((|t_as,us_as,k_as|), a_si) = initiator_init a srv b in
  let ((|t_bs,us_bs,k_bs|), b_si) = responder_init b srv in
  let before_idx_state_e = global_timestamp () in
  let ((|t_es,us_es,k_es|), e_si) = responder_init e srv in
  install_sk_at_auth_server #t_as #us_as srv a k_as;
  install_sk_at_auth_server #t_bs #us_bs srv b k_bs;
  install_sk_at_auth_server #t_es #us_es srv e k_es;

  let idx_comp_e = compromise e e_si 0 in

  let now = global_timestamp () in
  let k_es = query_secret_key (before_idx_state_e + 1) idx_comp_e now e e_si 0 in

  let msg1_idx = initiator_send_msg_1 a a_si in
  let (msg2_idx, _) = attacker_send_mal_msg_2 e srv msg1_idx k_es in
  let (srv_si, msg3_idx) = server_send_msg_3 srv msg2_idx in
  let (msg4_idx, conv_key) = attacker_send_msg_4 e b a msg3_idx k_es in

  // TODO: no mutual authentication either -> proof needed
  attacker_knows_conv_key_stored_in_initiator_or_responder_state a a_si conv_key

let benign () : LCrypto unit (pki oyrs_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get() in
  let x = benign_attacker () in
  print_trace ()

let intercept_msg_1 () : LCrypto unit (pki oyrs_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get() in
  let x = intercept_msg_1_attacker () in
  print_trace ()

let intercept_msg_2 () : LCrypto unit (pki oyrs_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get() in
  let x = intercept_msg_2_attacker () in
  print_trace ()

let impersonate_resp_to_init () : LCrypto unit (pki oyrs_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get() in
  let x = impersonate_resp_to_init_attacker () in
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
  IO.print_string "Finished Benign Attacker:\n";
  IO.print_string "Starting Intercept Msg1 Attacker:\n";
  assume(valid_trace (pki oyrs_preds) t0);
  let r,t1 = (reify (intercept_msg_1 ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Otway-Rees protocol.\n");
  IO.print_string "Finished Intercept Msg1 Attacker:\n";
  IO.print_string "Starting Intercept Msg2 Attacker:\n";
  assume(valid_trace (pki oyrs_preds) t0);
  let r,t1 = (reify (intercept_msg_2 ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Otway-Rees protocol.\n");
  IO.print_string "Finished Intercept Msg2 Attacker:\n";
  IO.print_string "Starting Impersonate Responder to Initiator Attacker:\n";
  assume(valid_trace (pki oyrs_preds) t0);
  let r,t1 = (reify (impersonate_resp_to_init ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Otway-Rees protocol.\n");
  IO.print_string "Finished Impersonate Responder to Initiator Attacker:\n"
