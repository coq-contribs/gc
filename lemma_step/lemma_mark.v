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
(*                              lemma_mark.v                                *)
(****************************************************************************)

Section lemma_mark.

Require Export gc.
Require Export reachable.
Require Export Sumbool.

Notation Reachable := (reachable node) (only parsing).

Lemma mark_ancestor :
 forall (s t : state) (n : node),
 mark_node s t ->
 forall m : node, reachable node (hp t) m n -> reachable node (hp s) m n.

intros s t n marknode m H_reach; elim marknode; clear marknode.
intros ctls ctlt heap H_grey; rewrite heap; assumption.
Qed.

Lemma grey_ancestor_col :
 forall (s t : state) (n : node),
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 hp s = hp t ->
 grey_node_case (mk s) (mk t) (hp s) ->
 forall m : node,
 reachable node (hp t) m n -> mk t m = white \/ mk t m = free.

intros s t n H_reach heap H m H_reach_m; elim H; clear H.
intros g mksg mktg mark1 mark2.
elim (eq_dec_node m g).
intro meqg; absurd (mk s g = grey); auto.
rewrite <- meqg; cut (mk s m = white \/ mk s m = free).
intro H; elim H; clear H; intro mksm; rewrite mksm; discriminate.
apply H_reach; rewrite heap; assumption.
intro mdifg; elim (sumbool_of_bool (hp s g m)); intro hsgm.
cut (reachable node (hp s) g n).
intro H_reach_g; absurd (mk s g = grey); auto.
elim (H_reach g H_reach_g); intro mksg2; rewrite mksg2; discriminate.
apply reach_true_reach with (m := m); auto.
rewrite heap; assumption.
rewrite <- (mark2 m); auto.
apply H_reach; rewrite heap; assumption.
Qed.

Hint Resolve grey_ancestor_col.

Lemma mark_ancestor_col :
 forall (s t : state) (n : node),
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 mark_node s t ->
 forall m : node,
 reachable node (hp t) m n -> mk t m = white \/ mk t m = free.

intros s t n H_reach marknode m H_reach_m; elim marknode; clear marknode.
intros ctls ctlt heap H_grey; eauto.
Qed.

Lemma grey_white :
 forall (s t : state) (n : node),
 mk s n = white ->
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 hp s = hp t -> grey_node_case (mk s) (mk t) (hp s) -> mk t n = white.

intros s t n mksn H_reach_s heap H_grey; elim H_grey; clear H_grey.
intros g mksg mktg mark1 mark2; elim (eq_dec_node n g).
intro neqg; absurd (mk s g = grey); auto.
rewrite <- neqg; rewrite mksn; discriminate.
intro ndifg; elim (sumbool_of_bool (hp s g n)); intro hsgn.
cut (reachable node (hp s) g n).
intro H_reach_g; absurd (mk s g = grey); auto.
elim (H_reach_s g H_reach_g); intro mksg2; rewrite mksg2; discriminate.
apply reach_true_reach with (m := n); auto.
constructor.
rewrite <- (mark2 n); auto.
Qed.

Hint Resolve grey_white.
                        
Lemma mark_white :
 forall (s t : state) (n : node),
 mk s n = white ->
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 mark_node s t -> mk t n = white.

intros s t n mksn H_reach_s marknode; elim marknode; clear marknode.
intros ctls ctlt heap H_grey; eauto.
Qed.

Lemma greynode_notfrees_notfreet :
 forall (s t : state) (n : node),
 mk s n <> free -> grey_node_case (mk s) (mk t) (hp s) -> mk t n <> free.

intros s t n mksn H_sons; elim H_sons; clear H_sons.
intros g mksg mktg case1 case2; elim (cases_marknode (mk s) (hp s) n g).
intro neqg; rewrite neqg; rewrite mktg; discriminate.
intro case; elim case; clear case.
intros ndifg case; elim case; clear case.
intro hsgnt; elim hsgnt; clear hsgnt.
intro case; rewrite (case1 n case); auto.
discriminate.
intro case; rewrite <- (case2 n); auto.
intro case; rewrite <- (case2 n); auto.
Qed.

Lemma marknode_notfrees_notfreet :
 forall s t : state,
 mark_node s t -> forall n : node, mk s n <> free -> mk t n <> free.

intros s t marknode n mksn; elim marknode; clear marknode.
intros ctls ctlt heap H_sons; apply (greynode_notfrees_notfreet s t n);
 assumption.
Qed.

Lemma marknode_accest_access :
 forall s t : state,
 mark_node s t ->
 forall n : node, accessible node (hp t) rt n -> accessible node (hp s) rt n.

intros s t marknode n acces_t_n; elim marknode; clear marknode.
intros ctls ctlt heap H_sons; elim H_sons; clear H_sons.
intros g mksg mktg H_col1 H_col2; rewrite heap; auto.
Qed.

Lemma marknode_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 mark_node s t -> ~ accessible node (hp t) rt n.

intros s t n notacces_n_s marknode; elim marknode; clear marknode.
intros ctls ctlt heap grey_node; rewrite <- heap; assumption.
Qed.

End lemma_mark.

Hint Resolve marknode_notaccess_notaccest.
Hint Resolve mark_ancestor_col.
Hint Resolve grey_ancestor_col.
Hint Resolve mark_white.
Hint Resolve grey_white.