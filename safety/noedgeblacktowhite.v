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
(*                           noedgeblacktowhite.v                           *)
(****************************************************************************)

Section invariant3.

Require Export gc.
Require Import Bool.
Require Export Sumbool.

Lemma imp1 :
 forall s : state, no_edge_black_to_white s -> no_edge_black_to_white_bis s.
               
unfold no_edge_black_to_white in |- *;
 unfold no_edge_black_to_white_bis in |- *.
intros s H n m mksn hsnm; intro mksm.
absurd (hp s n m = false).
intro hnmf.
apply (eq_true_false_abs (hp s n m)); assumption.
apply H; assumption.
Qed.


Lemma imp2 :
 forall s : state, no_edge_black_to_white_bis s -> no_edge_black_to_white s.

unfold no_edge_black_to_white_bis in |- *;
 unfold no_edge_black_to_white in |- *.
intros s H n mksn m mksm.
apply (not_true_is_false (hp s n m)).
intro hsnm.
absurd (mk s m = white); auto.
apply H with (n := n); assumption.
Qed.

Hint Resolve imp1.
Hint Resolve imp2.

Lemma no_edge_black_to_white_init :
 forall s : state, init_state s -> no_edge_black_to_white s.

unfold no_edge_black_to_white in |- *; unfold init_state in |- *.
intros s init n mksn m mksm.
elim init; clear init.
intros ctls init.
elim init; clear init; auto.
Qed.

Lemma initcolor_imp_noblack :
 forall m1 m2 : marking, init_color m1 m2 -> forall n : node, m2 n <> black.

unfold init_color in |- *; intros m1 m2 init n; elim init; clear init.
intros m2rt mark; elim mark; clear mark.
intros H_col1 H_col2; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; rewrite m2rt; discriminate.
intro ndifrt; elim (eq_dec_color (m1 n) black); intro m1n.
rewrite (H_col1 n); auto.
discriminate.
rewrite (H_col2 n); auto.
Qed.

Hint Immediate initcolor_imp_noblack.

Lemma no_edge_black_to_white_addedge :
 forall s t : state,
 no_edge_black_to_white s -> add_edge s t -> no_edge_black_to_white t.

unfold no_edge_black_to_white in |- *.
intros s t H_s addedge n mktn m mktm.
elim addedge; clear addedge; unfold marking_add in |- *; unfold add in |- *.
intros n0 m0 acces_s_n0 acces_s_m0 ctls ctlt add mark.
elim add; clear add.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htn0m0; elim mark; clear mark.
intro case1; elim case1; clear case1.
intros mksn0 mark; elim (eq_dec_node m0 m).
intro m0eqm; rewrite <- (H_heap1 n m).
apply H_s; rewrite <- mark; assumption.
intro neqn0; apply mksn0; rewrite <- neqn0; rewrite <- mark; assumption.
intro m0difm; rewrite <- (H_heap1 n m).
apply H_s; rewrite <- mark; assumption.
intro neqn0; apply mksn0; rewrite <- neqn0; rewrite <- mark; assumption.
intro case; elim case; clear case.
intro case2; elim case2; clear case2.
intros mksn0 mark; elim mark; clear mark.
intros mksm0 mark; elim (eq_dec_node n0 n).
intro n0eqn; rewrite <- n0eqn; rewrite <- (H_heap2 m).
apply H_s; auto.
rewrite <- mark; auto.
intro meqm0; apply mksm0; rewrite <- meqm0; rewrite <- mark; assumption.
intro n0difn; rewrite <- (H_heap1 n m); auto.
apply H_s; rewrite <- mark; assumption.
intro case3; elim case3; clear case3.
intros mksn0 mark; elim mark; clear mark; unfold update_color in |- *.
intros mksm0 mark; elim mark; clear mark.
intros mark mktm0; elim (eq_dec_node n0 n).
intro n0eqn; rewrite <- n0eqn; rewrite <- (H_heap2 m). 
apply H_s.
rewrite (mark n0); rewrite n0eqn; auto.
apply (noteqmar_noteqnod (mk t) n m0); rewrite mktn; rewrite mktm0;
 discriminate.
rewrite (mark m); auto.
apply (noteqmar_noteqnod (mk t) m m0); rewrite mktm; rewrite mktm0;
 discriminate.
apply (noteqmar_noteqnod (mk t) m m0); rewrite mktm; rewrite mktm0;
 discriminate.
intro n0difn; rewrite <- (H_heap1 n m); auto.
apply H_s.
rewrite (mark n); auto.
apply (noteqmar_noteqnod (mk t) n m0); rewrite mktn; rewrite mktm0;
 discriminate.
rewrite (mark m); auto.
apply (noteqmar_noteqnod (mk t) m m0); rewrite mktm; rewrite mktm0;
 discriminate.
Qed.

Lemma no_edge_black_to_white_removeedge :
 forall s t : state,
 no_edge_black_to_white s -> remove_edge s t -> no_edge_black_to_white t.

unfold no_edge_black_to_white in |- *.
intros s t H_s removeedge n mktn m mktm.
elim removeedge; clear removeedge; unfold remove in |- *.
intros n0 m0 acces_s_n0 acces_s_m0 ctls ctlt remove mark.
elim remove; clear remove.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htn0m0; elim (eq_dec_node n0 n).
intro n0eqn; elim (eq_dec_node m0 m).
intro m0eqm; rewrite <- n0eqn; rewrite <- m0eqm; assumption.
intro m0difm; rewrite <- n0eqn; rewrite <- (H_heap2 m); auto.
apply H_s.
rewrite n0eqn; rewrite <- mark; assumption.
rewrite <- mark; assumption.
intro n0difn; elim (eq_dec_node m0 m).
intro m0eqm; rewrite <- (H_heap1 n m); auto. 
apply H_s; rewrite <- mark; assumption.
intro m0difm; rewrite <- (H_heap1 n m); auto. 
apply H_s; rewrite <- mark; assumption.
Qed.

Lemma no_edge_black_to_white_alloc :
 forall s t : state,
 no_edge_black_to_white s -> alloc s t -> no_edge_black_to_white t.


unfold no_edge_black_to_white in |- *.
intros s t H_s alloc n mktn m mktm.
elim alloc; clear alloc; unfold update_color in |- *; unfold add in |- *;
 unfold remove in |- *.
intros ctls ctlt n0 mksn0 H_fils mark add; elim add; clear add.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htrtn0; elim mark; clear mark.
intros mark mktn0; elim (eq_dec_node n0 n).
intro n0eqn; elim (sumbool_of_bool (hp s n m)); intro hsnm.
rewrite <- n0eqn; elim H_fils with (fils := m).
intros heap1 heap2; elim heap2; clear heap2; auto.
rewrite n0eqn; assumption.
elim (eq_dec_node rt n).
intro rteqn; rewrite <- rteqn; rewrite <- (H_heap2 m).
rewrite rteqn; assumption.
apply (noteqmar_noteqnod (mk t) m n0); rewrite mktm; rewrite mktn0;
 discriminate.
intro rtdifn; rewrite <- (H_heap1 n m); auto.
intro n0difn; replace (hp t n m) with (hp s n m).
apply H_s.
rewrite (mark n); auto.
rewrite (mark m); auto.
apply (noteqmar_noteqnod (mk t) m n0); rewrite mktm; rewrite mktn0;
 discriminate.
elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; apply H_heap2.
apply (noteqmar_noteqnod (mk t) m n0); rewrite mktm; rewrite mktn0;
 discriminate.
auto.
Qed.

Lemma black_grey_node :
 forall (s t : state) (n m : node),
 (forall n m : node, mk s n = black -> hp s n m = true -> mk s m <> white) ->
 hp s = hp t ->
 grey_node_case (mk s) (mk t) (hp s) ->
 mk t n = black -> hp t n m = true -> mk t m <> white.

intros s t n m H_s heap H_sons mktn htnm; elim H_sons; clear H_sons.
intros g mksg mktg H_col1 H_col2; elim (cases_marknode (mk s) (hp s) m g).
intro meqg; rewrite meqg; rewrite mktg; discriminate.
intro case2; elim case2; clear case2.
intros mdifg H_heap_col; elim H_heap_col; clear H_heap_col.
intro hsgmt; elim hsgmt; clear hsgmt.
intro case2; rewrite (H_col1 m case2); discriminate.
intro case3; elim case3; clear case3.
intros hsgm mksm; rewrite <- (H_col2 m); auto.
intro hsgm; elim (cases_marknode (mk s) (hp s) n g).
intro neqg; absurd (hp s g m = false); auto.
intro hsgm2; apply (eq_true_false_abs (hp s g m)); auto.
rewrite heap; rewrite <- neqg; assumption.
intro case2; elim case2; clear case2.
intros ndifg H_heap_col; elim H_heap_col; clear H_heap_col.
intro hsgnt; elim hsgnt; clear hsgnt.
intro case2; absurd (mk t n = grey).
rewrite mktn; discriminate.
apply H_col1; assumption.
intro case3; rewrite <- (H_col2 m); auto.
apply H_s with (n := n).
rewrite (H_col2 n); auto.
rewrite heap; assumption.
intro hsgn; rewrite <- (H_col2 m); auto.
apply H_s with (n := n).
rewrite (H_col2 n); auto.
rewrite heap; assumption.
Qed.

Lemma no_edge_black_to_white_gccall :
 forall s t : state,
 no_edge_black_to_white_bis s -> gc_call s t -> no_edge_black_to_white_bis t.

unfold no_edge_black_to_white_bis in |- *.
intros s t H_s gccall n m mktn htnm; elim gccall; clear gccall.
intros ctls ctlt heap H_col init; absurd (mk t n = black); auto.
eauto.
intros ctls ctlt heap H_sons; apply (black_grey_node s t n m); auto.
unfold update_color in |- *; intros ctls ctlt heap H_col m0 mksm0 mark.
elim mark; clear mark.
intros mark mktm0; rewrite <- (mark m).
apply H_s with (n := n).
rewrite (mark n); auto.
apply (noteqmar_noteqnod (mk t) n m0); rewrite mktn; rewrite mktm0;
 discriminate.
rewrite heap; assumption.
cut (mk s m <> white).
intro mksm; intro meqm0; apply mksm; rewrite meqm0; assumption.
apply H_s with (n := n).
rewrite (mark n); auto.
apply (noteqmar_noteqnod (mk t) n m0); rewrite mktn; rewrite mktm0;
 discriminate.
rewrite heap; assumption.
Qed.

Lemma no_edge_black_to_white_marknode :
 forall s t : state,
 no_edge_black_to_white_bis s ->
 mark_node s t -> no_edge_black_to_white_bis t.

unfold no_edge_black_to_white_bis in |- *.
intros s t H_s marknode.
elim marknode; clear marknode.
intros ctls ctlt heap H_sons n m mktn htnm; apply (black_grey_node s t n m);
 auto.
Qed.

Lemma no_edge_black_to_white_gcstop :
 forall s t : state,
 no_edge_black_to_white s -> gc_stop s t -> no_edge_black_to_white t.

unfold no_edge_black_to_white in |- *; intros s t H_s gcstop; elim gcstop;
 clear gcstop.
intros ctls ctlt heap mark; rewrite heap; rewrite mark; assumption.
Qed.

Lemma no_edge_black_to_white_gcfree :
 forall s t : state,
 no_edge_black_to_white s -> gc_free s t -> no_edge_black_to_white t.

unfold no_edge_black_to_white in |- *.
intros s t H_s gcfree.
elim gcfree; clear gcfree.
unfold update_color in |- *.
intros ctls ctlt H_col heap m mksm mark n mktn m0 mktm0.
elim mark; clear mark.
intros mark mktm; rewrite heap; apply H_s.
rewrite (mark n); auto.
apply (noteqmar_noteqnod (mk t) n m); rewrite mktn; rewrite mktm;
 discriminate.
rewrite (mark m0); auto.
apply (noteqmar_noteqnod (mk t) m0 m); rewrite mktm0; rewrite mktm;
 discriminate.
Qed.

Hint Resolve no_edge_black_to_white_gcfree.

Lemma no_edge_black_to_white_gcfree_bis :
 forall s t : state,
 no_edge_black_to_white_bis s -> gc_free s t -> no_edge_black_to_white_bis t.

intros s t H_s gcfree; eauto.
Qed.

Lemma no_edge_black_to_white_gcfree1 :
 forall s t : state,
 no_edge_black_to_white s -> gc_free1 s t -> no_edge_black_to_white t.

unfold no_edge_black_to_white in |- *.
intros s t H_s gcfree1 n mktn m mktm.
elim gcfree1; clear gcfree1; unfold update_color in |- *.
intros ctls ctlt heap n0 mksn0 mark; elim mark; clear mark.
intros mark mktn0; rewrite <- heap; apply H_s.
rewrite (mark n); auto.
apply (noteqmar_noteqnod (mk t) n n0); rewrite mktn; rewrite mktn0;
 discriminate.
rewrite (mark m); auto.
apply (noteqmar_noteqnod (mk t) m n0); rewrite mktm; rewrite mktn0;
 discriminate.
Qed.

Lemma no_edge_black_to_white_gcend :
 forall s t : state,
 no_edge_black_to_white s -> gc_end s t -> no_edge_black_to_white t.

unfold no_edge_black_to_white in |- *; intros s t H_s gcend; elim gcend;
 clear gcend.
intros ctls ctlt heap mark; rewrite heap; rewrite mark; assumption.
Qed. 

End invariant3.

Hint Resolve imp1.
Hint Resolve imp2.
Hint Resolve no_edge_black_to_white_addedge.
Hint Resolve no_edge_black_to_white_removeedge.
Hint Resolve no_edge_black_to_white_alloc.
Hint Resolve no_edge_black_to_white_gccall.
Hint Resolve no_edge_black_to_white_marknode.
Hint Resolve no_edge_black_to_white_gcstop.
Hint Resolve no_edge_black_to_white_gcfree.
Hint Resolve no_edge_black_to_white_gcfree1.
Hint Resolve no_edge_black_to_white_gcend.