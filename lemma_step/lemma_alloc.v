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
(*                               lemma_alloc.v                              *)
(****************************************************************************)

Section lemma_alloc.

Require Export gc.
Require Export Bool.
Require Export Sumbool.
Require Export reachable.

Notation Reachable := (reachable node) (only parsing).

Lemma alloc_blacks_blackt :
 forall (s t : state) (n : node),
 mk s n = black -> alloc s t -> mk t n = black.

intros s t n mksn alloc; elim alloc; clear alloc.
intros ctls ctlt m mksm H_fils upd_col add; elim upd_col; clear upd_col.
intros mark mktm; elim (eq_dec_node n m).
intros neqm; rewrite neqm; assumption.
intro ndifm; rewrite <- (mark n ndifm); assumption.
Qed.

Lemma alloc_accest_access :
 forall (s t : state) (n0 : node),
 mk s n0 = free ->
 (forall fils : node, hp s n0 fils = true -> remove (hp s) (hp t) n0 fils) ->
 update_color (mk s) (mk t) black n0 ->
 add (hp s) (hp t) rt n0 ->
 forall n : node,
 accessible node (hp t) rt n -> n <> n0 -> accessible node (hp s) rt n.

intros s t n0 mksn0 H_fils mark add; simple induction 1.
intro rtdifn0; constructor.
intros n1 m acces_t_m H_ind htmn1 n1difn0; elim add; clear add.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htrtn0.
unfold remove in H_fils.
unfold accessible in |- *; apply reachable_edge with (m := m).
apply H_ind.
elim (eq_dec_node m n0); auto.
intro meqn0; rewrite meqn0 in htmn1; intro meqn02;
 apply (eq_true_false_abs (hp t n0 n1)); auto.
elim (sumbool_of_bool (hp s n0 n1)); intro hsn0n1.
elim (H_fils n1); auto.
intros H_heap_1 H_heap_2; elim H_heap_2; clear H_heap_2; auto.
elim (eq_dec_node n0 rt).
intro n0eqrt; rewrite n0eqrt; rewrite <- (H_heap2 n1 n1difn0);
 rewrite <- n0eqrt; assumption.
intro n0difrt; rewrite <- (H_heap1 n0 n1 n0difrt); assumption.
elim (eq_dec_node m rt).
intro meqrt; rewrite meqrt; rewrite (H_heap2 n1 n1difn0); rewrite <- meqrt;
 assumption.
intro mdifrt; rewrite (H_heap1 m n1 mdifrt); assumption.
Qed.

Lemma alloc_notgreyt_notgreys :
 forall s t : state,
 alloc s t -> forall n : node, mk t n <> grey -> mk s n <> grey.

intros s t alloc n mktn; elim alloc; clear alloc.
intros ctls ctlt n0 mksn0 H_fils mark add; elim mark; clear mark.
intros mark mktn0; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; rewrite mksn0; discriminate.
intro ndifn0; rewrite (mark n ndifn0); assumption.
Qed.

Lemma alloc_greys_greyt :
 forall s t : state,
 alloc s t -> forall n : node, mk s n = grey -> mk t n = grey.

intros s t alloc n mksn; elim alloc; clear alloc.
intros ctls ctlt n0 mksn0 Hfils mark add; elim mark; clear mark.
intros mark mktn0; rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n n0); rewrite mksn; rewrite mksn0;
 discriminate.
Qed.

Lemma alloc_notgreys_notgreyt :
 forall s t : state,
 alloc s t -> forall n : node, mk s n <> grey -> mk t n <> grey.

intros s t alloc n mksn; elim alloc; clear alloc.
intros ctls ctlt n0 mksn0 Hfils mark add; elim mark; clear mark.
intros mark mktn0; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; rewrite mktn0; discriminate.
intro ndifn0; rewrite <- (mark n ndifn0); assumption.
Qed.

Lemma alloc_notwhites_notwhitet :
 forall s t : state,
 alloc s t -> forall n : node, mk s n <> white -> mk t n <> white.

intros s t alloc n mksn; elim alloc; clear alloc.
intros ctls ctlt n0 mksn0 Hfils mark add; elim mark; clear mark.
intros mark mktn0; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; rewrite mktn0; discriminate.
intro ndifn0; rewrite <- (mark n ndifn0); assumption.
Qed.

Lemma alloc_whites_whitet :
 forall s t : state,
 alloc s t -> forall n : node, mk s n = white -> mk t n = white.

intros s t alloc n mksn; elim alloc; clear alloc.
intros ctls ctlt n0 mksn0 Hfils mark add; elim mark; clear mark.
intros mark mktn0; rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n n0); rewrite mksn; rewrite mksn0;
 discriminate.
Qed.

Lemma alloc_nogrey :
 forall s t : state,
 (forall n : node, mk s n <> grey) ->
 alloc s t -> forall n : node, mk t n <> grey.

intros s t H_s alloc n; apply (alloc_notgreys_notgreyt s t); auto.
Qed.

Lemma alloc_nowhite :
 forall s t : state,
 (forall n : node, mk s n <> white) ->
 alloc s t -> forall n : node, mk t n <> white.

intros s t H_s alloc n; apply (alloc_notwhites_notwhitet s t); auto.
Qed.

Lemma alloc_ancestor :
 forall (s t : state) (n : node),
 ~ accessible node (hp t) rt n ->
 alloc s t ->
 forall m : node, reachable node (hp t) m n -> reachable node (hp s) m n.

intros s t n notacc_n_t alloc m H_reach; elim alloc; clear alloc.
intros ctls ctlt n' mksn' H_fils upd_col add; elim add; clear add.
intros heap1 H; elim H; clear H.
intros heap2 htrtn'; generalize notacc_n_t; elim H_reach; try constructor.
clear notacc_n_t; intros n'' m' H_reach_m' H_ind htm'n'' H_acc.
apply reachable_edge with (m := m').
apply H_ind.
intro H_acc_m'; apply H_acc; unfold accessible in |- *;
 apply reachable_edge with (m := m'); assumption.
rewrite (heap1 m' n''); try assumption.
intro m'eqrt; absurd (accessible node (hp t) rt rt); try constructor.
rewrite <- m'eqrt; intro H_acc_m'; apply H_acc; unfold accessible in |- *;
 apply reachable_edge with (m := m'); try assumption.
rewrite m'eqrt; constructor.
Qed.

Lemma alloc_ancestor_col :
 forall (s t : state) (n : node),
 ~ accessible node (hp t) rt n ->
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 alloc s t ->
 forall m : node,
 reachable node (hp t) m n -> mk t m = white \/ mk t m = free.

intros s t n notacc_n H_reach alloc m H_reach_m_t; elim alloc; clear alloc.
intros ctls ctlt n' mksn' H_fils upd_col add; elim upd_col.
intros mark mktn'; rewrite <- mark.
apply H_reach; apply alloc_ancestor with (t := t); try assumption.
apply alloc_add_free_to_rt with (n := n'); try assumption.
intro meqn'; elim add; clear add.
intros heap1 H; elim H; clear H.
intros heap2 htrtn'; absurd (accessible node (hp t) rt n').
rewrite <- meqn'.
apply reach_notacc with (n := n); assumption.
unfold accessible in |- *; apply reachable_edge with (m := rt);
 [ constructor | assumption ].
Qed.

End lemma_alloc.

Hint Resolve alloc_nogrey.
Hint Resolve alloc_whites_whitet.
Hint Resolve alloc_blacks_blackt.
Hint Resolve alloc_nowhite.
Hint Resolve alloc_ancestor_col.