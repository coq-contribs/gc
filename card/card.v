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
(*                               card.v                                     *)
(****************************************************************************)

Section cardinal.

Require Import Arith.
Require Export lemme_arith.

Variables (A B : Set) (P : B -> Prop).

Axiom eq_dec_set : forall a b : A, {a = b} + {a <> b}.

Lemma dif :
 forall (M : A -> B) (a1 a2 : A), P (M a1) -> ~ P (M a2) -> a1 <> a2.

intros M a1 a2 Ma1 Ma2.
intro a1eqa2.
apply Ma2.
rewrite <- a1eqa2; assumption.
Qed.

Lemma dif2 :
 forall (M : A -> B) (a1 a2 : A), P (M a1) -> ~ P (M a2) -> a2 <> a1.

intros M a1 a2 Ma1 Ma2.
intro a2eqa1.
apply Ma2; rewrite a2eqa1; assumption.
Qed.

Inductive card : (A -> B) -> nat -> Prop :=
  | card_0 : forall M : A -> B, (forall a : A, ~ P (M a)) -> card M 0
  | card_S :
      forall (M1 M2 : A -> B) (nb : nat) (a0 : A),
      card M1 nb ->
      (forall a : A, a <> a0 -> M1 a = M2 a) ->
      ~ P (M1 a0) -> P (M2 a0) -> card M2 (S nb).


Definition update (M : A -> B) (a0 : A) (b : B) (a : A) :=
  match eq_dec_set a a0 with
  | left _ => b
  | right _ => M a
  end.

Lemma exist_updated :
 forall (b : B) (M : A -> B) (a0 : A),
 exists M' : A -> B, (forall a : A, a <> a0 -> M a = M' a) /\ M' a0 = b.

intros b M a0.
split with (update M a0 b).
unfold update in |- *.
split.
intros a adifa0.
case (eq_dec_set a a0); auto.
intro aeqa0; elim adifa0; assumption.
case (eq_dec_set a0 a0); auto.
intro a0difa0.
absurd (a0 = a0); auto.
Qed.


Lemma card_inv :
 forall (M1 : A -> B) (nb : nat),
 card M1 nb ->
 forall M2 : A -> B,
 (forall a : A, ~ P (M1 a) -> ~ P (M2 a)) ->
 (forall a : A, P (M1 a) -> P (M2 a)) -> card M2 nb.

simple induction 1; clear H M1 nb.
intros M Ma M2 H_PM_PM2_dif H_PM_PM2.
constructor 1.
intro a; apply H_PM_PM2_dif; auto.
intros M1 M2 nb a0 card_M1 H_ind H_M1_M2 M1a0 M2a0 M3 H_M2_M3_dif H_M2_M3.
elim (exist_updated (M1 a0) M3 a0).
intros M4 H.
elim H; clear H.
intros H_M3_M4 M4a0.
apply card_S with (M1 := M4) (a0 := a0).
apply H_ind.
intros a M1a.
elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; rewrite M4a0; assumption.
intro adifa0; rewrite <- (H_M3_M4 a adifa0).
apply (H_M2_M3_dif a).
rewrite <- (H_M1_M2 a adifa0); assumption.
intros a M1a.
rewrite <- (H_M3_M4 a).
apply (H_M2_M3 a).
rewrite <- (H_M1_M2 a).
assumption.
apply (dif M1 a a0); auto.
apply (dif M1 a a0); auto.
intros a adifa0; symmetry  in |- *; apply (H_M3_M4 a); assumption.
rewrite M4a0; assumption.
apply (H_M2_M3 a0); assumption.
Qed.


Lemma card_rem :
 forall (M1 : A -> B) (nb : nat),
 card M1 nb ->
 forall (M2 : A -> B) (a0 : A),
 (forall a : A, a <> a0 -> M1 a = M2 a) ->
 P (M1 a0) -> ~ P (M2 a0) -> card M2 (pred nb).

intros M1 nb H.
elim H; clear H M1 nb.
intros M Ma M2 a0 H_M_M2 Ma0 M2a0.
absurd (P (M a0)); auto.
intros M1 M2 nb a0.
generalize (refl_equal nb); pattern nb at -1 in |- *; case nb.
intros nbeq0 card_M1 H_ind H_M1_M2 M1a0 M2a0 M3 a1 H_M2_M3 M2a1 M3a1.
elim (eq_dec_set a0 a1).
simpl in |- *.
intro a0eqa1.
constructor 1.
intro a.
elim (eq_dec_set a a1).
intro aeqa1.
rewrite aeqa1; assumption.
intro adifa1.
rewrite <- (H_M2_M3 a adifa1).
rewrite a0eqa1 in H_M1_M2.
inversion card_M1; clear card_M1.
rewrite <- (H_M1_M2 a adifa1); auto.
intro a0difa1.
inversion card_M1; clear card_M1. 
absurd (P (M1 a1)); auto.
rewrite (H_M1_M2 a1); auto.
intros nb' nbSn card_M1 H_ind H_M1_M2 M1a0 M2a0 M3 a1 H_M2_M3 M2a1 M3a1.
elim (exist_updated (M1 a0) M3 a0).
intros M4 H.
elim H; clear H.
intros H_M3_M4 M4a0.
elim (eq_dec_set a0 a1).
intro a0eqa1.
rewrite <- a0eqa1 in H_M2_M3; rewrite <- a0eqa1 in M3a1.
simpl in |- *.
apply card_inv with (M1 := M1); auto.
intros a M1a.
elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; assumption.
intro adifa0.
rewrite <- (H_M2_M3 a adifa0); rewrite <- (H_M1_M2 a adifa0); assumption.
intros a M1a.
rewrite <- (H_M2_M3 a).
rewrite <- (H_M1_M2 a).
assumption.
apply (dif M1 a a0); auto.
apply (dif M1 a a0); auto.
intro a0difa1.
rewrite (pred_S (S nb')).
apply card_S with (M1 := M4) (a0 := a0).
apply H_ind with (a0 := a1).
intros a adifa1.
elim (eq_dec_set a a0).
intro aeqa0; rewrite aeqa0; symmetry  in |- *; assumption.
intro adifa0.
rewrite <- (H_M3_M4 a adifa0); rewrite <- (H_M2_M3 a adifa1).
apply (H_M1_M2 a); auto.
rewrite (H_M1_M2 a1); auto.
rewrite <- (H_M3_M4 a1); auto.
intros a adifa0; symmetry  in |- *; apply (H_M3_M4 a); auto.
rewrite M4a0; assumption.
rewrite <- (H_M2_M3 a0); auto.
auto with arith.
Qed.

Lemma unicity_card :
 forall (M : A -> B) (nb : nat),
 card M nb -> forall nb' : nat, card M nb' -> nb = nb'.


simple induction 1; clear H nb M.
intros M Ma nb' card_M.
inversion_clear card_M; auto.
absurd (P (M a0)); auto.
intros M1 M2 nb a0 card_M1 H_ind H_M1_M2 M1a0 M2a0 nb' card_M2.
generalize (refl_equal nb'); pattern nb' at -1 in |- *; case nb'.
intros nb'eq0.
rewrite nb'eq0 in card_M2.
inversion card_M2.
absurd (P (M2 a0)); auto.
intros n nb'Sn.
rewrite (eqnm_eqSnSm nb n); auto.
apply H_ind.
replace n with (pred nb').
apply card_rem with (M1 := M2) (a0 := a0); auto.
intros a adifa0.
symmetry  in |- *.
apply H_M1_M2; assumption.
symmetry  in |- *.
apply (S_pred n nb'); auto.
Qed.

End cardinal.
