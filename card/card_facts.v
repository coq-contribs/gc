(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*              Solange Coupet-Grimal & Catherine Nouvet                    *)
(*                                                                          *)
(*                                                                          *)
(*       Laboratoire d'Informatique Fondamentale de Marseille               *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*           Contact :Solange.Coupet@cmi.univ-mrs.fr                        *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V7.0                                  *)
(*                             Septembre 2002                               *)
(*                                                                          *)
(****************************************************************************)
(*                               card_facts.v                               *)
(****************************************************************************)

Section card_facts.

Require Import Arith.
Require Import card.

Variable A B C : Set.

Notation Card := (card _ _) (only parsing).

Axiom eq_dec_set : forall a b : A, {a = b} + {a <> b}.

Definition prop_dec (P : B -> Prop) := forall b : B, {P b} + {~ P b}.

Definition prop_dec2 (P : C -> Prop) := forall c : C, {P c} + {~ P c}.

Definition update_M (b : B) (M : A -> B) (a0 a : A) :=
  match eq_dec_set a a0 with
  | right _ => M a
  | left _ => b
  end.

Lemma exist_updated_M :
 forall (M : A -> B) (a0 : A) (b : B),
 exists M' : A -> B, (forall a : A, a <> a0 -> M a = M' a) /\ M' a0 = b.

intros M a0 b.
split with (update_M b M a0).
unfold update_M in |- *; split.
intros a adifa0; case (eq_dec_set a a0); auto.
intro aeqa0; absurd (a = a0); auto.
case (eq_dec_set a0 a0); auto.
intro adifa0; absurd (a0 = a0); auto.
Qed.



Definition update_N (c0 : C) (N : A -> C) (a0 a : A) :=
  match eq_dec_set a a0 with
  | right _ => N a
  | left _ => c0
  end.

Lemma exist_updated_N :
 forall (N : A -> C) (a0 : A) (c0 : C),
 exists N' : A -> C, (forall a : A, a <> a0 -> N a = N' a) /\ N' a0 = c0.

intros N a0 c0.
split with (update_N c0 N a0).
unfold update_N in |- *; split.
intros a adifa0; case (eq_dec_set a a0); auto.
intro aeqa0; absurd (a = a0); auto.
case (eq_dec_set a0 a0); auto.
intro adifa0; absurd (a0 = a0); auto.
Qed.


Lemma include_card :
 forall (P Q : B -> Prop) (nb : nat) (M : A -> B),
 prop_dec Q ->
 (forall b : B, Q b -> P b) ->
 card _ _ P M nb -> exists nb' : nat, card _ _ Q M nb' /\ nb' <= nb.
       
intros P Q nb M dec H_P_Q card_P_M.
induction  card_P_M as [M H| M1 M2 nb a0 card_P_M Hreccard_P_M H H0 H1].
exists 0; split; auto.
constructor.
intro a; intro QMa; absurd (P (M a)); auto.
elim Hreccard_P_M; clear Hreccard_P_M.
intros nb' H2; elim H2; clear H2.
intros card_Q_M1 le_nb'_nb.
unfold prop_dec in dec.
elim dec with (b := M2 a0); intro QM2a0.
exists (S nb').
split.
apply card_S with (M1 := M1) (a0 := a0); auto.
auto with arith.
exists nb'.
split; auto.
apply card_inv with (M1 := M1); auto.
intros a QM1a.
elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; assumption.
intro adifa0; rewrite <- (H a adifa0); assumption.
intros a QM1a.
rewrite <- (H a); auto.
intro aeqa0; apply H0; apply H_P_Q; rewrite aeqa0 in QM1a; assumption.
Qed.


Lemma include_card_bis :
 forall (P : B -> Prop) (Q : C -> Prop) (M : A -> B) (nb : nat),
 (exists c0 : C, ~ Q c0) ->
 prop_dec2 Q ->
 card _ _ P M nb ->
 forall N : A -> C,
 (forall a : A, Q (N a) -> P (M a)) ->
 exists nb' : nat, card _ _ Q N nb' /\ nb' <= nb.

intros P Q M nb H_Q dec card_P_M.
induction  card_P_M as [M H| M1 M2 nb a0 card_P_M Hreccard_P_M H H0 H1].
intros N H_Q_P; exists 0; split; auto.
constructor.
intro a; intro QNa; absurd (P (M a)); auto.
intros N H_Q_P.
elim H_Q; clear H_Q.
intros c0 Q_c0.
elim (exist_updated_N N a0 c0); intros N' H_N'.
elim H_N'; clear H_N'.
intros H_N_N' N'a0; rewrite <- N'a0 in Q_c0.
unfold prop_dec2 in dec; elim (dec (N a0)).
intro Q_N_a0.
cut (exists nb' : nat, card A C Q N' nb' /\ nb' <= nb).
intro card_Q_N'; elim card_Q_N'; clear card_Q_N'.
intros nb' H_nb'; elim H_nb'; clear H_nb'.
intros card_Q_N' le_nb'_nb.
exists (S nb'); split; auto with arith.
apply card_S with (M1 := N') (a0 := a0); auto.
intros a aeqa0; symmetry  in |- *; apply (H_N_N' a); auto.
apply Hreccard_P_M.
intro a; elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; intro QN'a0; absurd (Q (N' a0)); auto.
intro adifa0; rewrite <- (H_N_N' a adifa0); rewrite (H a adifa0); auto.
intro Q_N_a0.
cut (exists nb' : nat, card A C Q N' nb' /\ nb' <= nb).
intro card_Q_N'; elim card_Q_N'; clear card_Q_N'.
intros nb' H_nb'; elim H_nb'; clear H_nb'.
intros card_Q_N' le_nb'_nb.
exists nb'; split; auto with arith.
apply card_inv with (M1 := N'); auto.
intros a Q_N'_a; elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; auto.
intro adifa0; rewrite (H_N_N' a adifa0); assumption.
intro a; elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; intro QN'a0; absurd (Q (N' a0)); auto.
intros adifa0 Q_N'_a; rewrite (H_N_N' a adifa0); assumption.
apply Hreccard_P_M.
intro a; elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; intro QN'a0; absurd (Q (N' a0)); auto.
intro adifa0; rewrite <- (H_N_N' a adifa0); rewrite (H a adifa0); auto.
Qed.


End card_facts.