module YLM.Sessions


open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib

module M = YLM.Messages
module LC = LabeledCryptoAPI
module LR = LabeledRuntimeAPI


(* Yahalom specific aliases *)

let is_labeled i b l = LC.is_labeled M.ylm_global_usage i b l
let is_lt_key i b p srv = LC.is_aead_key M.ylm_global_usage i b (readers [P p; P srv]) "YLM.lt_key"
let is_comm_key i b srv p q = LC.is_aead_key M.ylm_global_usage i b (readers [P srv; P p; P q]) "YLM.comm_key"

let lt_key i p srv = b:bytes{is_lt_key i b p srv}

noeq type session_st =
  (* Auth server session for secret keys shared with principals *)
  | AuthServerSession: p:principal -> k_ps:bytes -> session_st
  (* Principal secret key session with auth server *)
  | PKeySession: srv:principal -> k_ps:bytes -> session_st
  (* Protocol states *)
  | InitiatorSentMsg1: b:principal -> n_a:bytes -> session_st
  | ResponderSentMsg2: a:principal -> srv:principal -> n_b:bytes -> session_st
  | AuthServerSentMsg3: a:principal -> b:principal -> k_ab:bytes -> session_st
  | InitiatorSentMsg4: b:principal -> srv:principal -> k_ab:bytes -> session_st
  | ResponderRecvedMsg4: a:principal -> srv:principal -> k_ab:bytes -> session_st

let valid_session (i:nat) (p:principal) (si vi:nat) (st:session_st) =
  match st with
  | AuthServerSession pri k_pri_srv ->
    M.is_msg i k_pri_srv (readers [P p]) /\ is_lt_key i k_pri_srv pri p
  | PKeySession srv k_ps -> is_lt_key i k_ps p srv
  | InitiatorSentMsg1 b n_a -> is_labeled i n_a public
  | ResponderSentMsg2 a srv n_b -> is_labeled i n_b (readers [P p; P a; P srv])
  | AuthServerSentMsg3 a b k_ab -> is_comm_key i k_ab p a b
  | InitiatorSentMsg4 b srv k_ab ->
    M.is_msg i k_ab (readers [P p]) /\
    (is_labeled i k_ab (readers [P srv; P p; P b]) \/ LC.corrupt_id i (P srv) \/ LC.corrupt_id i (P p))
  | ResponderRecvedMsg4 a srv k_ab ->
    M.is_msg i k_ab (readers [P p]) /\
    (is_labeled i k_ab (readers [P srv; P a; P p]) \/ LC.corrupt_id i (P srv) \/ LC.corrupt_id i (P a) \/ LC.corrupt_id i (P p))

let valid_session_later (i j:timestamp) (p:principal) (si vi:nat) (st:session_st) :
  Lemma (ensures (valid_session i p si vi st /\ later_than j i ==> valid_session j p si vi st))
= ()

val serialize_session_st: i:nat -> p:principal -> si:nat -> vi:nat -> st:session_st{valid_session i p si vi st} -> M.msg i (readers [V p si vi])

val parse_session_st: sst:bytes -> result session_st

val parse_serialize_session_st_lemma: i:nat -> p:principal -> si:nat -> vi:nat -> st:session_st ->
    Lemma (requires (valid_session i p si vi st))
	  (ensures  (Success st == parse_session_st (serialize_session_st i p si vi st)))
	  [SMTPat (parse_session_st (serialize_session_st i p si vi st))]


let epred idx s e =
  match e with
  | ("initiate",[a_bytes;b_bytes;srv_bytes;n_a]) ->
    bytes_to_string a_bytes == Success s
  | ("req_key",[a_bytes;b_bytes;srv_bytes;n_a;n_b]) -> (
    match (bytes_to_string a_bytes, bytes_to_string b_bytes, bytes_to_string srv_bytes) with
    | (Success a, Success b, Success srv) ->
      b = s /\
      M.is_msg idx n_a public /\
      was_rand_generated_before idx n_b (readers [P b; P a; P srv]) (nonce_usage "YLM.nonce_b")
    | _ -> False
  )
  | ("send_key",[a_bytes;b_bytes;srv_bytes;n_a;n_b;k_ab]) -> (
    match (bytes_to_string a_bytes, bytes_to_string b_bytes, bytes_to_string srv_bytes) with
    | (Success a, Success b, Success srv) ->
      srv = s /\
      was_rand_generated_before idx k_ab (readers [P srv; P a; P b]) (aead_usage "YLM.comm_key") /\
      (did_event_occur_before idx b (M.event_req_key a b srv n_a n_b) \/
      (LC.corrupt_id idx (P b) \/ LC.corrupt_id idx (P srv)) /\ M.is_msg idx n_b public)
    | _ -> False
  )
  | ("fwd_key",[a_bytes;b_bytes;srv_bytes;n_a;n_b;k_ab]) -> (
    match (bytes_to_string a_bytes, bytes_to_string b_bytes, bytes_to_string srv_bytes) with
    | (Success a, Success b, Success srv) ->
      a = s /\
      (did_event_occur_before idx srv (M.event_send_key a b srv n_a n_b k_ab) \/
      LC.corrupt_id idx (P a) \/ LC.corrupt_id idx (P srv))
    | _ -> False
  )
  | _ -> False

let ylm_session_st_inv (trace_idx:nat) (p:principal) (state_session_idx:nat) (version:nat) (state:bytes) =
    M.is_msg trace_idx state (readers [V p state_session_idx version]) /\
    (match parse_session_st state with
     | Success state -> valid_session trace_idx p state_session_idx version state
     | _ -> True)

let ylm_preds: LR.preds = {
  LR.global_usage = M.ylm_global_usage;
  LR.trace_preds = {
    LR.can_trigger_event = epred;
    LR.session_st_inv = ylm_session_st_inv;
    LR.session_st_inv_later = (fun i j p si vi sst ->
      match parse_session_st sst with
      | Success st -> valid_session_later i j p si vi st
      | _ -> ()
    );
    LR.session_st_inv_lemma = (fun i p si vi sst -> ())
  }
}
