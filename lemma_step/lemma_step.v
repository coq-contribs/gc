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
(*                              lemma_step.v                                *)
(****************************************************************************)

Section lemma_step.

Require Export lemma_add.
Require Export lemma_remove.
Require Export lemma_alloc.
Require Export lemma_call.
Require Export lemma_mark.
Require Export lemma_stop.
Require Export lemma_free.
Require Export lemma_free1.
Require Export lemma_end.

Lemma initcolor_notfrees_notfreet :
 forall (s t : state) (n : node),
 mk s n <> free -> init_color (mk s) (mk t) -> mk t n <> free.

unfold init_color in |- *; intros s t n mksn init; elim init; clear init.
intros mktrt H_heap; elim H_heap; clear H_heap.
intros H_heap1 H_heap2; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; rewrite mktrt; discriminate.
intro ndifrt; elim (eq_dec_color (mk s n) black); intro mksnb.
rewrite (H_heap1 n); auto.
discriminate.
rewrite (H_heap2 n); auto.
Qed.


Lemma color_node :
 forall (n : node) (m : marking),
 m n = black \/ m n = grey \/ m n = white \/ m n = free.

intros n m.
case (m n).
right.
right.
left.
trivial.
left.
trivial.
right.
left.
trivial.
right.
right.
right.
trivial.
Qed.


Lemma trivial :
 forall (n : node) (m : marking),
 m n <> free -> m n <> white -> m n <> grey -> m n = black.

intros n m mnf mnw mng; elim (color_node n m); trivial.
intro mn; elim mn; clear mn.
intro mng2; absurd (m n = grey); assumption.
intro mn; elim mn; clear mn.
intro mnw2; absurd (m n = white); assumption.
intro mnf2; absurd (m n = free); assumption.
Qed.


Lemma ind :
 forall s : state,
 rt_grey_or_black s ->
 no_edge_black_to_white_bis s ->
 acc_imp_notfree s ->
 (forall n : node, mk s n <> grey) ->
 forall n : node, accessible node (hp s) rt n -> mk s n = black.

unfold rt_grey_or_black in |- *; unfold no_edge_black_to_white_bis in |- *;
 unfold acc_imp_notfree in |- *.
intros s inv1_s inv2_s inv3_s H_col n acces_s_n; elim acces_s_n;
 clear acces_s_n.
elim inv1_s.
intro mksrt.
absurd (mk s rt = grey).
auto.
assumption.
trivial.
intros n0 m acces_s_m mksm hsmn0.
cut (mk s n0 <> white /\ mk s n0 <> grey /\ mk s n0 <> free).
intro mksn0.
elim mksn0; clear mksn0.
intros mksn0w mksn0; elim mksn0; clear mksn0.
intros mksn0g mksn0f; apply (trivial n0 (mk s)); assumption.
split.
apply inv2_s with (n := m); assumption.
split; auto.
apply inv3_s; unfold accessible in |- *; apply reachable_edge with (m := m);
 assumption.
Qed.

End lemma_step.