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
open DS.Messages
open DS.Sessions
open DS.Protocol
open DS.Attacker


val benign_attacker:
  unit ->
  LCrypto unit (pki ds_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

#set-options "--z3rlimit 200 --max_fuel 4 --max_ifuel 2"
let benign_attacker () =
  let a:principal = "alice" in
  let b:principal = "bob" in

  let now = global_timestamp () in
  let sigk_a_idx = gen_private_key #ds_preds #now a SIG "DS.sig_key" in
  let now = global_timestamp () in
  let sk_b_idx = gen_private_key #ds_preds #now b PKE "DS.pke_key" in
  let now = global_timestamp () in
  let sigk_srv_idx = gen_private_key #ds_preds #now auth_srv SIG "DS.sig_key" in

  let now = global_timestamp () in
  let pk_a_srv_idx = install_public_key #ds_preds #now a auth_srv SIG "DS.sig_key" in
  let now = global_timestamp () in
  let pk_b_srv_idx = install_public_key #ds_preds #now b auth_srv PKE "DS.pke_key" in
  let now = global_timestamp () in
  let verk_srv_a_idx = install_public_key #ds_preds #now auth_srv a SIG "DS.sig_key" in
  let now = global_timestamp () in
  let verk_srv_b_idx = install_public_key #ds_preds #now auth_srv b SIG "DS.sig_key" in

  let (msg1_idx, a_sess_idx) = initiator_send_msg_1 a b in
  let (msg2_idx, srv_sess_idx, c_sm2) = server_send_msg_2 msg1_idx in
  let (msg3_idx, c_sm3) = initiator_send_msg_3 c_sm2 a msg2_idx a_sess_idx in
  let (b_sess_idx, c_end) = responder_recv_msg_3 c_sm3 b msg3_idx in
  ()

val fake_cert_attacker:
  unit ->
  LCrypto unit (pki ds_preds)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let fake_cert_attacker () =
   let a:principal = "alice" in
  let b:principal = "bob" in
  let e:principal = "eve" in

  let now = global_timestamp () in
  let sigk_a_idx = gen_private_key #ds_preds #now a SIG "DS.sig_key" in
  let now = global_timestamp () in
  let sk_b_idx = gen_private_key #ds_preds #now b PKE "DS.pke_key" in
  let before_sk_e = global_timestamp () in
  let sk_e_idx = gen_private_key #ds_preds #before_sk_e e PKE "DS.pke_key" in
  let before_sigk_srv = global_timestamp () in
  let sigk_srv_idx = gen_private_key #ds_preds #before_sigk_srv auth_srv SIG "DS.sig_key" in

  let t_pk_a = global_timestamp () in
  let pk_a_srv_idx = install_public_key #ds_preds #t_pk_a a auth_srv SIG "DS.sig_key" in
  let now = global_timestamp () in
  let pk_b_srv_idx = install_public_key #ds_preds #now b auth_srv PKE "DS.pke_key" in
  let t_pk_e = global_timestamp () in
  let pk_e_srv_idx = install_public_key #ds_preds #t_pk_e e auth_srv PKE "DS.pke_key" in
  let now = global_timestamp () in
  let verk_srv_a_idx = install_public_key #ds_preds #now auth_srv a SIG "DS.sig_key" in
  let now = global_timestamp () in
  let verk_srv_b_idx = install_public_key #ds_preds #now auth_srv b SIG "DS.sig_key" in

  // compromise eve's secret key
  let idx_comp_e = compromise e sk_e_idx 0 in
  let after_comp_sk_e = global_timestamp () in
  let sk_e = query_secret_key (before_sk_e + 1) idx_comp_e after_comp_sk_e e sk_e_idx 0 in
  print_string "compromised eve's secret key\n";

  // compromise server's sign key and pub keys of eve and alice
  let idx_comp_srv = compromise auth_srv sigk_srv_idx 0 in
  let after_comp_sigk_srv = global_timestamp () in
  let sigk_srv = query_secret_key (before_sigk_srv + 1) idx_comp_srv after_comp_sigk_srv auth_srv sigk_srv_idx 0 in
  print_string "compromised server's sign key\n";

  let idx_comp_srv = compromise auth_srv pk_e_srv_idx 0 in
  let after_comp_pk_e = global_timestamp () in
  let pk_e = query_public_key t_pk_e idx_comp_srv after_comp_pk_e auth_srv pk_e_srv_idx 0 in
  print_string "queried eve's public key in server state\n";

  let idx_comp_srv = compromise auth_srv pk_a_srv_idx 0 in
  let after_comp_pk_a = global_timestamp () in
  let pk_a = query_public_key t_pk_a idx_comp_srv after_comp_pk_a auth_srv pk_a_srv_idx 0 in
  print_string "queried alice's public key in server state\n";

  let sigk_srv = pub_bytes_later after_comp_sigk_srv after_comp_pk_a sigk_srv in
  let pk_e = pub_bytes_later after_comp_pk_e after_comp_pk_a pk_e in
  let sk_e = pub_bytes_later after_comp_sk_e after_comp_pk_a sk_e in

  let (msg1_idx, a_sess_idx) = initiator_send_msg_1 a b in
  let (|msg2_idx,c_sm2|) = attacker_issue_fake_cert e sigk_srv pk_a pk_e msg1_idx in
  let (msg3_idx, c_sm3) = initiator_send_msg_3 c_sm2 a msg2_idx a_sess_idx in
  let (|t_ck,ck|) = attacker_recv_msg_3 e sk_e msg3_idx in

  attacker_knows_comm_key_stored_in_initiator_state a a_sess_idx ck

let benign () : LCrypto unit (pki ds_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get () in
  let x = benign_attacker () in
  print_trace ()

let fake_cert () : LCrypto unit (pki ds_preds)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= print_string "start\n";
  let t0 = get () in
  let x = fake_cert_attacker () in
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
  IO.print_string "Finished Benign Attacker:\n";
  IO.print_string "Starting Fake Certificate Attacker:\n";
  assume(valid_trace (pki ds_preds) t0);
  let r,t1 = (reify (fake_cert ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN: Successful execution of Denning-Sacco protocol.\n");
  IO.print_string "Finished Fake Certificate Attacker:\n"
