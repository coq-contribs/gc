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
(*                              lib_minus.v                                 *)
(****************************************************************************)

Section lib_minus.

Require Import Arith.

Lemma minus_pred : forall n m : nat, n - S m = pred (n - m). 

simple induction n; simple induction m.
simpl in |- *; auto.
intros n0 H_ind_n; auto with arith.
simpl in |- *; auto with arith.
intros n1 H_ind_m; replace (S n0 - S n1) with (n0 - n1); auto with arith.
rewrite <- (H n1); auto with arith.
Qed.


Lemma pred_S_minus : forall n m : nat, n - S m = pred n - m.

intros n m.
induction  n as [| n Hrecn].
simpl in |- *; trivial.
simpl in |- *; trivial.
Qed.


End lib_minus.