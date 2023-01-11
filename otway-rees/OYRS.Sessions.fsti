module OYRS.Sessions


open SecrecyLabels
open CryptoLib

module MSG = OYRS.Messages
module LC = LabeledCryptoAPI
module LR = LabeledRuntimeAPI


(* Otway-Rees specific aliases *)
// TODO: move to common util module

let is_labeled i b l = LC.is_labeled MSG.oyrs_global_usage i b l

let str_to_bytes #i s = LC.string_to_bytes #(MSG.oyrs_global_usage) #i s
let concat #i #l b1 b2 = LC.concat #(MSG.oyrs_global_usage) #i #l b1 b2


noeq type session_st =
  (* Auth server session for secret keys shared with principals *)
  | AuthServerSession: p:principal -> k_ps:bytes -> session_st
  (* Initial knowledge of principals *)
  | InitiatorInit: srv:principal -> k_as:bytes -> b:principal -> session_st
  | ResponderInit: srv:principal -> k_bs:bytes -> session_st
  (* Protocol states *)
  | InitiatorSentMsg1: srv:principal -> k_as:bytes -> b:principal -> c:bytes -> n_a:bytes -> session_st
  | ResponderSentMsg2: srv:principal -> k_bs:bytes -> a:principal -> c:bytes -> n_b:bytes -> session_st
  | AuthServerSentMsg3: a:principal -> b:principal -> c:bytes -> n_a:bytes -> n_b:bytes -> k_ab:bytes -> session_st
  | ResponderSentMsg4: srv:principal -> a:principal -> k_ab:bytes -> session_st
  | InitiatorRecvedMsg4: srv:principal -> b:principal -> k_ab:bytes -> session_st

val valid_session: i:nat -> p:principal -> si:nat -> vi:nat -> st:session_st -> Type0

val serialize_session_st: i:nat -> p:principal -> si:nat -> vi:nat -> st:session_st{valid_session i p si vi st} -> MSG.msg i (readers [V p si vi])

val parse_session_st: sst:bytes -> result session_st

val parse_serialize_session_st_lemma: i:nat -> p:principal -> si:nat -> vi:nat -> st:session_st ->
    Lemma (requires (valid_session i p si vi st))
	  (ensures  (Success st == parse_session_st (serialize_session_st i p si vi st)))
	  [SMTPat (parse_session_st (serialize_session_st i p si vi st))]


let oyrs_session_st_inv (trace_idx:nat) (p:principal) (state_session_idx:nat) (version:nat) (state:bytes) =
    MSG.is_msg trace_idx state (readers [V p state_session_idx version]) /\
    (match parse_session_st state with
     | Success s -> valid_session trace_idx p state_session_idx version s
     | _ -> True)

val valid_session_later: i:timestamp -> j:timestamp -> p:principal -> si:nat -> vi:nat -> st:session_st ->
  Lemma (ensures (valid_session i p si vi st /\ later_than j i ==> valid_session j p si vi st))

let oyrs_session_st_inv_later (i:timestamp) (j:timestamp) (p:principal) (si:nat) (vi:nat) (state:bytes) :
  Lemma ((oyrs_session_st_inv i p si vi state /\ later_than j i) ==> oyrs_session_st_inv j p si vi state)
= // Proving the first clause
  LC.can_flow_later i j (readers [V p si vi]) (readers [V p si vi]);
  LC.is_valid_later MSG.oyrs_global_usage i j state;
  assert(MSG.is_msg i state (readers [V p si vi]) /\ later_than j i ==> MSG.is_msg j state (readers [V p si vi]));
  // Second clause
  match parse_session_st state with
  | Success st -> valid_session_later i j p si vi st;()
  | _ -> ()

let oyrs_preds: LR.preds = {
  LR.global_usage = MSG.oyrs_global_usage;
  LR.trace_preds = {
    LR.can_trigger_event = (fun idx s e -> False);
    LR.session_st_inv = oyrs_session_st_inv;
    LR.session_st_inv_later = oyrs_session_st_inv_later;
    LR.session_st_inv_lemma = (fun i p si vi st -> ())
  }
}
