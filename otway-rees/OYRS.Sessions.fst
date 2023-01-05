module OYRS.Sessions


let valid_session i p si vi st =
  match st with
  | AuthServerSession pri k_pri_srv -> is_labeled i k_pri_srv (readers [P pri; P p])
  | InitiatorInit srv k_as b -> is_labeled i k_as (readers [P p; P srv])
  | ResponderInit srv k_bs -> is_labeled i k_bs (readers [P p; P srv])
  | InitiatorSentMsg1 srv k_as b c n_a ->
    is_labeled i k_as (readers [P p; P srv]) /\
    is_labeled i c public /\
    is_labeled i n_a (readers [P p; P srv])
  | ResponderSentMsg2 srv k_bs a c n_b ->
    is_labeled i k_bs (readers [P p; P srv]) /\
    is_labeled i c public /\
    is_labeled i n_b (readers [P p; P srv])
  | AuthServerSentMsg3 a b c n_a n_b k_ab ->
    is_labeled i c public /\
    is_labeled i n_a (readers [P a; P p]) /\
    is_labeled i n_b (readers [P b; P p]) /\
    is_labeled i k_ab (readers [P p; P a; P b])
  | ResponderSentMsg4 srv a k_ab -> is_labeled i k_ab (readers [P srv; P a; P p])
  | InitiatorRecvedMsg4 srv b k_ab -> is_labeled i k_ab (readers [P srv; P p; P b])
