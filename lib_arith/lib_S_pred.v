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
(*                              lib_S_pred.v                                *)
(****************************************************************************)

Section lib_S_pred.

Require Import Arith.

Lemma pred_S : forall n : nat, n <> 0 -> pred (S n) = S (pred n).

intros n nO.
generalize (refl_equal n); pattern n at -1 in |- *; case n.
intro ndifO.
absurd (n = 0); auto.
intros n0 nSn0.
simpl in |- *; trivial.
Qed.


Lemma eqnm_eqSnSm : forall n m : nat, n = m -> S n = S m.

auto with arith.
Qed.


Lemma S_pred : forall n m : nat, S n = m -> n = pred m.

intros n m.
generalize (refl_equal n); pattern n at -1 in |- *; case n.
intros neq0 meq1.
rewrite <- meq1; auto.
intros n0 nSn0 meqSSn0.
rewrite <- meqSSn0.
simpl in |- *; auto.
Qed.


End lib_S_pred.