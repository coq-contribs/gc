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
(*                             lemma_remove.v                               *)
(****************************************************************************)

Section lemma_remove.

Require Export gc.
Require Export Bool.
Require Export reachable.

Notation Reachable := (reachable node) (only parsing).

Lemma remove_accest_access :
 forall s t : state,
 remove_edge s t ->
 forall n : node, accessible node (hp t) rt n -> accessible node (hp s) rt n.

unfold accessible in |- *; intros s t removeedge n acces_t_n; elim removeedge;
 clear removeedge; unfold remove in |- *.
unfold accessible in |- *;
 intros n0 m acces_s_n0 acces_s_m ctls ctlt remove mark; 
 elim remove; clear remove.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htn0m; elim acces_t_n; clear acces_t_n.
constructor.
intros n1 m0 acces_t_n1 acces_s_n1 htn1m0;
 apply reachable_edge with (m := m0); auto.
elim (eq_dec_node m0 n0).
intro m0eqn0; rewrite m0eqn0; rewrite (H_heap2 n1).
rewrite <- m0eqn0; assumption.
intro n1eqm; apply (eq_true_false_abs (hp t m0 n1)); auto.
rewrite m0eqn0; rewrite n1eqm; assumption.
intro m0difn0; rewrite (H_heap1 m0 n1); auto.
Qed.

Lemma remove_notfrees_notfreet :
 forall s t : state,
 remove_edge s t -> forall n : node, mk s n <> free -> mk t n <> free.

intros s t removeedge n mksn; elim removeedge; clear removeedge.
intros n0 m acces_s_n0 acces_s_m ctls ctlt remove mark; rewrite mark;
 assumption.
Qed.

Lemma remove_blacks_blackt :
 forall s t : state,
 remove_edge s t -> forall n : node, mk s n = black -> mk t n = black.

intros s t removeedge n mksn; elim removeedge; clear removeedge.
intros n0 m acces_s_n0 acces_s_m ctls ctlt remove mark; rewrite mark;
 assumption.
Qed.

Lemma remove_notgreyt_notgreys :
 forall s t : state,
 remove_edge s t -> forall n : node, mk t n <> grey -> mk s n <> grey.

intros s t removeedge n mksn; elim removeedge; clear removeedge.
intros n0 m acces_s_n0 acces_s_m ctls ctlt remove mark; rewrite <- mark;
 assumption.
Qed.

Lemma remove_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 remove_edge s t -> ~ accessible node (hp t) rt n. 

unfold accessible in |- *; intros s t n not_acces_n_s removeedge;
 elim removeedge; clear removeedge.
unfold accessible in |- *;
 intros n1 n2 acces_n1_s acces_n2_s ctls ctlt remove mark; 
 elim remove; clear remove.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htn1n2; intro acces_n_t; inversion acces_n_t.
rewrite <- H in not_acces_n_s; absurd (accessible node (hp s) rt rt); auto.
constructor.
elim (eq_dec_node m n1).
intro meqn1; elim (eq_dec_node n n2).
intro neqn2; rewrite meqn1 in H0; rewrite neqn2 in H0;
 apply (eq_true_false_abs (hp t n1 n2)); assumption.
intro ndifn2; absurd (accessible node (hp s) rt n); auto.
unfold accessible in |- *; apply reachable_edge with (m := m).
replace (reachable node (hp s) rt m) with (accessible node (hp s) rt m); auto.
apply (remove_accest_access s t); auto.
apply (remove_to_node s t n1 n2); auto.
unfold remove in |- *; auto.
rewrite meqn1; rewrite meqn1 in H0; rewrite (H_heap2 n ndifn2); assumption.
intro mdifn1; absurd (accessible node (hp s) rt n); auto.
unfold accessible in |- *; apply reachable_edge with (m := m).
replace (reachable node (hp s) rt m) with (accessible node (hp s) rt m); auto.
apply (remove_accest_access s t); auto.
apply (remove_to_node s t n1 n2); auto.
unfold remove in |- *; auto.
rewrite (H_heap1 m n mdifn1); assumption.
Qed.

Lemma remove_white :
 forall (s t : state) (n : node),
 mk s n = white -> remove_edge s t -> mk t n = white.

intros s t n mksn removeedge; elim removeedge; clear removeedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt remove mark; rewrite mark;
 assumption.
Qed.

Lemma remove_nogrey :
 forall s t : state,
 (forall n : node, mk s n <> grey) ->
 remove_edge s t -> forall n : node, mk t n <> grey.

intros s t mksn removeedge n; elim removeedge; clear removeedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt remove mark; rewrite mark; auto.
Qed.

Lemma remove_nowhite :
 forall s t : state,
 (forall n : node, mk s n <> white) ->
 remove_edge s t -> forall n : node, mk t n <> white.

intros s t mksn removeedge n; elim removeedge; clear removeedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt remove mark; rewrite mark; auto.
Qed.

Lemma remove_ancestor :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 remove_edge s t ->
 forall m : node, reachable node (hp t) m n -> reachable node (hp s) m n.

intros s t n notacc_n_s removeedge m H_reach; elim removeedge;
 clear removeedge.
intros n1 n2 acc_n1_s acc_n2_s ctls ctlt remove mark; elim remove;
 clear remove.
intros heap1 H; elim H; clear H.
intros heap2 htn1n2; generalize notacc_n_s.
elim H_reach; try constructor.
clear H_reach notacc_n_s n; intros n' m' H_reach H_ind htm'n' H_acc;
 elim (eq_dec_node m' n1).
intro m'eqn1; elim (eq_dec_node n' n2).
intro n'eqn2; absurd (accessible node (hp s) rt n2); auto.
rewrite n'eqn2 in H_acc; assumption.
intro n'difn2; apply reachable_edge with (m := m').
apply H_ind; intro H_acc'; apply H_acc.
unfold accessible in |- *; apply reachable_edge with (m := m'); auto.
rewrite m'eqn1 in htm'n'; rewrite m'eqn1; rewrite (heap2 n' n'difn2);
 assumption.
rewrite m'eqn1 in htm'n'; rewrite m'eqn1; rewrite (heap2 n' n'difn2);
 assumption.
intro m'difn1; apply reachable_edge with (m := m').
apply H_ind; intro H_acc'; apply H_acc.
unfold accessible in |- *; apply reachable_edge with (m := m'); auto.
rewrite (heap1 m' n' m'difn1); assumption.
rewrite (heap1 m' n' m'difn1); assumption.
Qed.

Lemma remove_ancestor_col :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 remove_edge s t ->
 forall m : node,
 reachable node (hp t) m n -> mk t m = white \/ mk t m = free.

intros s t n notacc_n_s H_reach_col removeedge; elim removeedge;
 clear removeedge.
intros n1 n2 acc_n1_s acc_n2_s ctls ctlt remove mark m H_reach; rewrite mark;
 apply H_reach_col.
apply remove_ancestor with (t := t); auto.
apply remove_to_node with (n := n1) (n' := n2); auto.
Qed.

End lemma_remove.

Hint Resolve remove_notaccess_notaccest.
Hint Resolve remove_white.
Hint Resolve remove_nogrey.
Hint Resolve remove_blacks_blackt.
Hint Resolve remove_nowhite.
Hint Resolve remove_ancestor_col.