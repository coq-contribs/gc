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
(*                               lib_plus.v                                 *)
(****************************************************************************)

Section lib_plus.

Require Import Arith.
Require Export lib_S_pred.

Lemma plus_S_pred : forall n m : nat, m <> 0 -> n + m = S n + pred m.

intros n m mO.
generalize (refl_equal m); pattern m at -1 in |- *; case m.
intro meqO.
absurd (m = 0); assumption.
intros n0 mSn0.
rewrite <- (pred_Sn n0).
simpl in |- *; auto.
Qed.

Lemma plus_O : forall n m : nat, n <> 0 -> n + m <> 0.

intros n m; induction  m as [| m Hrecm].
intro ndif0; rewrite <- (plus_n_O n); auto.
intro ndif0.
rewrite <- (plus_n_Sm n m); auto with arith.
Qed.

Lemma plus_O_O : forall n m : nat, n + m = 0 -> m = 0.

intros n.
induction  n as [| n Hrecn].
intro m.
rewrite (plus_comm 0 m).
replace (m + 0) with m; auto.
intro m.
intro plus_Sn_m.
absurd (S n + m = 0); auto.
absurd (S n <= S n + m); auto with arith.
rewrite plus_Sn_m; auto with arith.
Qed.


Lemma plus_pred : forall n m : nat, m <> 0 -> pred (n + m) = n + pred m.

intros n m mO.
generalize (refl_equal m); pattern m at -1 in |- *; case m.
intro meqO.
absurd (m = 0); auto.
intros n0 mSn0.
rewrite <- (pred_Sn n0).
rewrite <- (plus_n_Sm n n0).
rewrite <- (pred_Sn (n + n0)); reflexivity.
Qed.

Lemma pred_plus_S :
 forall n m : nat, n <> 0 -> pred (n + S m) = S (pred (n + m)).

intros n m; induction  m as [| m Hrecm].
intro ndifO.
rewrite <- (plus_n_Sm n 0); rewrite <- (pred_S (n + 0)); trivial.
apply (plus_O n 0); auto.
intro ndifO.
rewrite <- (plus_n_Sm n (S m)); rewrite <- (pred_S (n + S m)); auto.
apply (plus_O n (S m)); auto.
Qed.

Lemma pred_plus_minus :
 forall n g w : nat,
 g <> 0 -> n <= w -> pred (g + w) = pred (g + n) + (w - n).

simple induction n; simple induction w.
intros gdif0 le_0_0; simpl in |- *; auto with arith.
intros n0 H_ind gdif0 le_0_Sn0; rewrite <- (plus_n_O g);
 rewrite <- (minus_n_O (S n0)); rewrite (plus_comm g (S n0));
 rewrite (plus_pred (S n0) g); auto.
rewrite (plus_comm (S n0) (pred g)); auto.
intros gdif0_bis le_Sn0_0; absurd (S n0 <= 0); auto with arith.
intros n1 H_ind gdif0 le_Sn0_n1; replace (S n1 - S n0) with (n1 - n0);
 auto with arith.
rewrite <- (plus_n_Sm g n0); rewrite (pred_S (g + n0)).
rewrite (plus_Snm_nSm (pred (g + n0)) (n1 - n0));
 rewrite <- (plus_n_Sm (pred (g + n0)) (n1 - n0)); 
 rewrite <- (H g n1); auto.
rewrite <- (pred_S (g + n1)); auto.
intro plus_g_n1; absurd (g = 0); auto.
rewrite (plus_comm g n1) in plus_g_n1; apply (plus_O_O n1 g); auto.
auto with arith.
intro plus_g_n0; absurd (g = 0); auto.
rewrite (plus_comm g n0) in plus_g_n0; apply (plus_O_O n0 g); auto.
Qed.


End lib_plus.