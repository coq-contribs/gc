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
(*                               lemma_add.v                                *)
(****************************************************************************)

Section lemma_add.

Require Export gc.
Require Export reachable.

Notation Reachable := (reachable node) (only parsing).

Lemma add_notacc_white :
 forall (s t : state) (n : node),
 mk s n = white ->
 ~ accessible node (hp s) rt n -> add_edge s t -> mk t n = white.

intros s t n mksn notacc_n_s addedge; elim addedge; clear addedge.
intros n1 n2 acc_n1_s acc_n2_s ctls ctlt add H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 mark; rewrite mark; assumption.
intro H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 mark; rewrite mark; assumption.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 H; elim H; clear H.
intros mark mktn2; elim (eq_dec_node n n2).
intro neqn2; rewrite neqn2 in notacc_n_s;
 absurd (accessible node (hp s) rt n2); assumption.
intro ndifn2; rewrite <- (mark n ndifn2); assumption.
Qed.

Lemma add_nogrey :
 forall s t : state,
 nogrey_accn_imp_blackn s ->
 (forall n : node, mk s n <> grey) ->
 add_edge s t -> forall n : node, mk t n <> grey.

unfold nogrey_accn_imp_blackn in |- *; intros s t H_inv H_col addedge n;
 elim addedge; clear addedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark; elim mark; clear mark.
intro H; elim H; clear H.
intros mksn1 mark; rewrite mark; auto.
intro H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 mark; rewrite mark; auto.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 upd_col; elim upd_col; clear upd_col.
intros mark mktn2; elim (eq_dec_node n n2).
intro neqn2; absurd (mk s n2 = white); auto.
rewrite H_inv; [ discriminate | auto | auto ].
intro ndifn2; rewrite <- (mark n ndifn2); auto.
Qed.

Lemma add_nowhite :
 forall s t : state,
 (forall n : node, mk s n <> white) ->
 add_edge s t -> forall n : node, mk t n <> white.

unfold nogrey_accn_imp_blackn in |- *; intros s t H_white addedge n;
 elim addedge; clear addedge.
intros n1 n2 acc_n1_s acc_n2_s ctls ctlt add H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 mark; rewrite mark; auto.
intro H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 mark; rewrite mark; auto.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 H; absurd (mk s n2 = white); auto.
Qed.
                    
Lemma add_accest_access :
 forall s t : state,
 add_edge s t ->
 forall n : node, accessible node (hp t) rt n -> accessible node (hp s) rt n.

unfold accessible in |- *; intros s t addedge n acces_t_n; elim addedge;
 clear addedge; unfold add in |- *.
unfold accessible in |- *;
 intros n0 m0 acces_s_n0 acces_s_m0 ctls ctlt add mark; 
 elim add; clear add.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htn0m0; elim acces_t_n.
constructor.
intros n1 m acces_t_n1 acces_s_n1 htn1m; elim (eq_dec_node n1 m0).
intro n1eqm0; rewrite n1eqm0; assumption.
intro n1difm0; apply reachable_edge with (m := m); auto.
elim (eq_dec_node m n0).
intro meqn0; rewrite meqn0; rewrite (H_heap2 n1 n1difm0); rewrite <- meqn0;
 assumption.
intro mdifn0; rewrite (H_heap1 m n1 mdifn0); assumption.
Qed.

Lemma add_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 add_edge s t -> ~ accessible node (hp t) rt n. 

unfold accessible in |- *; intros s t n not_acces_n_s addedge; elim addedge;
 clear addedge.
unfold accessible in |- *;
 intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark; 
 elim add; clear add.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2. 
intros H_heap2 htn1n2; intro acces_n_t; inversion acces_n_t.
rewrite <- H in not_acces_n_s; absurd (accessible node (hp s) rt rt); auto.
constructor.
elim (eq_dec_node m n1).
intro meqn1; elim (eq_dec_node n n2).
intro neqn2; rewrite neqn2 in not_acces_n_s;
 absurd (accessible node (hp s) rt n2); auto.
intro ndifn2; absurd (accessible node (hp s) rt n); auto.
unfold accessible in |- *; rewrite meqn1 in H0;
 apply reachable_edge with (m := n1); auto.
rewrite (H_heap2 n ndifn2); assumption.
intro mdifn1; absurd (accessible node (hp s) rt n); auto.
unfold accessible in |- *; apply reachable_edge with (m := m).
replace (reachable node (hp s) rt m) with (accessible node (hp s) rt m); auto.
apply (add_accest_access s t); auto.
apply (add_to_node s t n1 n2); auto.
unfold add in |- *; auto.
rewrite (H_heap1 m n mdifn1); assumption.
Qed.

Lemma add_ancestor :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 add_edge s t ->
 forall m : node, reachable node (hp t) m n -> reachable node (hp s) m n.

intros s t n notacc_n_s addedge m H_reach; elim addedge; clear addedge.
intros n1 n2 acc_n1_s acc_n2_s ctls ctlt add mark; elim add; clear add.
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

Lemma add_ancestor_col :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 add_edge s t ->
 forall m : node,
 reachable node (hp t) m n -> mk t m = white \/ mk t m = free.

intros s t n notacc_n_s H_anc addedge; elim addedge; clear addedge.
intros n1 n2 acc_n1_s acc_n2_s ctls ctlt add H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 mark m H_anc_m_t; rewrite mark; apply H_anc.
apply add_ancestor with (t := t); try assumption.
apply add_to_node with (n := n1) (n' := n2); try assumption.
constructor; auto.
intros H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 mark m H_anc_m_t; rewrite mark; apply H_anc.
apply add_ancestor with (t := t); try assumption.
apply add_to_node with (n := n1) (n' := n2); try assumption.
unfold marking_add in |- *; right; left; split; auto.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 H m H_anc_m_t; elim H; clear H.
intros mark mktn2; elim (eq_dec_node m n2).
intro meqn2; absurd (accessible node (hp s) rt n2); auto. 
rewrite <- meqn2; apply reach_notacc with (n := n); try assumption.
apply add_ancestor with (t := t); auto.
apply add_to_node with (n := n1) (n' := n2); try assumption.
unfold marking_add in |- *; right; right; split; auto.
split; auto.
unfold update_color in |- *; split; auto.
intro mdifn2; rewrite <- (mark m mdifn2); apply H_anc;
 apply add_ancestor with (t := t); auto.
apply add_to_node with (n := n1) (n' := n2); try assumption.
unfold marking_add in |- *; right; right; split; auto.
split; auto.
unfold update_color in |- *; split; auto.
Qed.

Lemma add_notgreyt_notgreys :
 forall s t : state,
 add_edge s t -> forall n : node, mk t n <> grey -> mk s n <> grey.

intros s t addedge n mktn; elim addedge; clear addedge;
 unfold marking_add in |- *.
intros n0 m acces_s_n0 acces_s_m ctls ctlt add mark; elim mark; clear mark.
intro case1; elim case1; clear case1.
intros mksn0 mark; rewrite <- mark; assumption.
intro case; elim case; clear case.
intro case2; elim case2; clear case2.
intros mksn0 mark; elim mark; clear mark.
intros mksm mark; rewrite <- mark; assumption.
intro case3; elim case3; clear case3.
intros mksn0 mark; elim mark; clear mark.
intros mksm mark; elim mark; clear mark.
intros mark mktm; rewrite (mark n); auto.
intro neqm; apply mktn; rewrite neqm; assumption.
Qed.

Lemma add_blacks_blackt :
 forall s t : state,
 add_edge s t -> forall n : node, mk s n = black -> mk t n = black.

intros s t addedge n mksn; elim addedge; clear addedge;
 unfold marking_add in |- *.
intros n0 m acces_s_n0 acces_s_m ctls ctlt add mark; elim mark; clear mark.
intro case1; elim case1; clear case1.
intros mksn0 mark; rewrite mark; assumption.
intro case; elim case; clear case.
intro case2; elim case2; clear case2.
intros mksn0 mark; elim mark; clear mark.
intros mksm mark; rewrite mark; assumption.
intro case3; elim case3; clear case3.
intros mksn0 mark; elim mark; clear mark.
intros mksm mark; elim mark; clear mark.
intros mark mktm; rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n m); rewrite mksn; rewrite mksm;
 discriminate.
Qed.

Lemma add_notfrees_notfreet :
 forall s t : state,
 add_edge s t -> forall n : node, mk s n <> free -> mk t n <> free.

intros s t addedge n mksn; elim addedge; clear addedge;
 unfold marking_add in |- *.
intros n0 m acces_s_n0 acces_s_m ctls ctlt add mark; elim mark; clear mark.
intro case1; elim case1; clear case1.
intros mksn0 mark; rewrite mark; assumption.
intro case; elim case; clear case.
intro case2; elim case2; clear case2.
intros mksn0 mark; elim mark; clear mark.
intros mksm mark; rewrite mark; assumption.
intro case3; elim case3; clear case3.
intros mksn0 mark; elim mark; clear mark.
intros mksm mark; elim mark; clear mark.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n); auto.
Qed.

Lemma add_white_nogrey :
 forall (s t : state) (n : node),
 mk s n = white ->
 ~ accessible node (hp s) rt n -> add_edge s t -> mk t n = white.

intros s t n mksn not_acces_n addedge; elim addedge; clear addedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark; elim mark; clear mark.
intro H; elim H; clear H.
intros mksn1 mark; rewrite mark; assumption.
intro H; elim H; clear H.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 mark; rewrite mark; assumption.
intro H; elim H; clear H.
intros mksn1 H; elim H; clear H.
intros mksn2 upd_col; elim upd_col; clear upd_col.
intros mark mktn2; elim (eq_dec_node n n2).
intro neqn2; rewrite neqn2 in not_acces_n;
 absurd (accessible node (hp s) rt n2); auto.
intro ndifn2; rewrite <- (mark n ndifn2); assumption.
Qed.

End lemma_add.

Hint Resolve add_notaccess_notaccest.
Hint Resolve add_nogrey.
Hint Resolve add_white_nogrey.
Hint Resolve add_blacks_blackt.
Hint Resolve add_nowhite.
Hint Resolve add_notacc_white.
Hint Resolve add_ancestor_col.