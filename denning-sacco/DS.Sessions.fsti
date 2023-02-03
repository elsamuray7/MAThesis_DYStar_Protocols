module DS.Sessions


open SecrecyLabels
open CryptoLib

module M = DS.Messages
module LC = LabeledCryptoAPI
module LR = LabeledRuntimeAPI


(* Denning-Sacco specific aliases *)

let is_labeled i b l = LC.is_labeled M.ds_global_usage i b l
/// Ensures 'b' is a Denning-Sacco communication key of 'p' and 'q'
let is_comm_key i b p q = LC.is_aead_key M.ds_global_usage i b (readers [P p; P q]) "DS.comm_key"

let str_to_bytes #i s = LC.string_to_bytes #(M.ds_global_usage) #i s
let concat #i #l b1 b2 = LC.concat #(M.ds_global_usage) #i #l b1 b2


noeq type session_st =
  | InitiatorSentMsg1: b:principal -> srv:principal -> session_st
  | AuthServerSentMsg2: a:principal -> b:principal -> session_st
  | InitiatorSentMsg3: b:principal -> ck:bytes -> session_st
  | ResponderRecvedMsg3: a:principal -> ck:bytes -> session_st

let valid_session (i:nat) (p:principal) (si vi:nat) (st:session_st) =
  match st with
  | InitiatorSentMsg3 b ck -> is_comm_key i ck p b
  | ResponderRecvedMsg3 a ck ->
    M.is_msg i ck (readers [P p]) /\
    (is_labeled i ck (readers [P a; P p]) \/ LC.corrupt_id i (P a) \/ LC.corrupt_id i (P p))
  | _ -> True

let valid_session_later (i j:timestamp) (p:principal) (si vi:nat) (st:session_st) :
  Lemma (ensures (valid_session i p si vi st /\ later_than j i ==> valid_session j p si vi st))
= ()

val serialize_session_st: i:nat -> p:principal -> si:nat -> vi:nat -> st:session_st{valid_session i p si vi st} -> M.msg i (readers [V p si vi])
val parse_session_st: sst:bytes -> result session_st

val parse_serialize_session_st_lemma: i:nat -> p:principal -> si:nat -> vi:nat -> st:session_st ->
    Lemma (requires (valid_session i p si vi st))
	  (ensures  (Success st == parse_session_st (serialize_session_st i p si vi st)))
	  [SMTPat (parse_session_st (serialize_session_st i p si vi st))]


let epred idx s e = True

let ds_session_st_inv (trace_idx:nat) (p:principal) (state_session_idx:nat) (version:nat) (state:bytes) =
  M.is_msg trace_idx state (readers [V p state_session_idx version]) /\
  (match parse_session_st state with
  | Success state -> valid_session trace_idx p state_session_idx version state
  | _ -> True)

let ds_preds: LR.preds = {
  LR.global_usage = M.ds_global_usage;
  LR.trace_preds = {
    LR.can_trigger_event = epred;
    LR.session_st_inv = ds_session_st_inv;
    LR.session_st_inv_later = (fun i j p si vi sst ->
      match parse_session_st sst with
      | Success st -> valid_session_later i j p si vi st
      | _ -> ()
    );
    LR.session_st_inv_lemma = (fun i p si vi sst -> ())
  }
}
