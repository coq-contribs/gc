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
(*                           nogreyaccnblackn.v                             *)
(****************************************************************************)

Section invariant5.

Require Export accnotfree.
Require Export noedgeblacktowhite.

Lemma nogrey_accn_imp_blackn_init :
 forall s : state, init_state s -> nogrey_accn_imp_blackn s.

unfold nogrey_accn_imp_blackn in |- *.
intros s init H_col n2 acces_s_n2.
elim init; clear init.
intros ctls H_mark_col.
elim H_mark_col; clear H_mark_col.
intros mark heap; elim mark; clear mark.
intros mksrt mark; elim acces_s_n2; auto.
intros n m acces_s_m mksm hsmn.
absurd (hp s m n = false); auto.
rewrite hsmn; discriminate.
Qed.

Lemma nogrey_accn_imp_blackn_addedge :
 forall s t : state,
 nogrey_accn_imp_blackn s -> add_edge s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *.
intros s t H_s addedge H_col n2 acces_t_n2.
apply (add_blacks_blackt s t); auto.
apply H_s.
intro n1; apply (add_notgreyt_notgreys s t); auto.
apply (add_accest_access s t); assumption.
Qed.

Lemma nogrey_accn_imp_blackn_removeedge :
 forall s t : state,
 nogrey_accn_imp_blackn s -> remove_edge s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *.
intros s t H_s removeedge H_col n2 acces_t_n2.
apply (remove_blacks_blackt s t); auto.
apply H_s.
intro n1; apply (remove_notgreyt_notgreys s t); auto.
apply (remove_accest_access s t); assumption.
Qed.

Lemma nogrey_accn_imp_blackn_alloc :
 forall s t : state,
 nogrey_accn_imp_blackn s -> alloc s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *.
intros s t H_s alloc H_col n2 acces_t_n2.
elim alloc; clear alloc.
intros ctls ctlt n mksn H_fils mark add; elim mark; clear mark.
intros mark mktn; elim (eq_dec_node n n2).
intro neqn2; rewrite <- neqn2; assumption.
intro ndifn2; rewrite <- (mark n2); auto.
apply H_s.
intro n1; apply (alloc_notgreyt_notgreys s t); auto.
apply (alloc_add_free_to_rt s t) with (n := n); auto.
unfold update_color in |- *; auto.
apply (alloc_accest_access s t n); auto.
unfold update_color in |- *; auto.
Qed.

Lemma nogrey_accn_imp_blackn_gccall :
 forall s t : state,
 rt_grey_or_black s ->
 no_edge_black_to_white_bis s ->
 acc_imp_notfree s ->
 nogrey_accn_imp_blackn s -> gc_call s t -> nogrey_accn_imp_blackn t.


unfold nogrey_accn_imp_blackn in |- *.
intros s t inv1_s inv2_s inv3_s H_s gccall H_col n2 acces_t_n2.
elim gccall; clear gccall.
intros ctls ctlt heap mark init; elim init; clear init.
intros mktrt H_mark_col; absurd (mk t rt = grey); auto.
intros ctls ctlt heap H_sons; apply (ind t); auto.
apply (rt_grey_or_black_gccall s t); auto.
apply (call_exist_grey s t); assumption.
apply (no_edge_black_to_white_gccall s t); auto.
apply (call_exist_grey s t); auto.
apply (acc_imp_notfree_gccall s t); auto.
apply (call_exist_grey s t); auto.
intros ctls ctlt heap H_col2 m mksm mark.
apply (updatecolor_blacks_blackt s t) with (m := m); auto.
apply H_s; auto.
rewrite heap; assumption.
Qed.

Lemma nogrey_accn_imp_blackn_marknode :
 forall s t : state,
 rt_grey_or_black s ->
 no_edge_black_to_white_bis s ->
 acc_imp_notfree s ->
 nogrey_accn_imp_blackn s -> mark_node s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *.
intros s t inv1_s inv2_s inv3_s H_s marknode H_col n2 acces_t_n2.
apply (ind t); auto.
apply (rt_grey_or_black_marknode s t); assumption.
apply (no_edge_black_to_white_marknode s t); assumption.
apply (acc_imp_notfree_marknode s t); assumption.
Qed.

Lemma nogrey_accn_imp_blackn_gcstop :
 forall s t : state,
 nogrey_accn_imp_blackn s -> gc_stop s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *.
intros s t H_s gcstop H_col n2 acces_t_n2.
apply (gcstop_blacks_blackt s t); auto.
apply H_s.
intro n1; apply (gcstop_notgreyt_notgreys s t); auto.
apply (gcstop_accest_access s t); auto.
Qed.

Lemma nogrey_accn_imp_blackn_gcfree :
 forall s t : state,
 nogrey_accn_imp_blackn s -> gc_free s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *.
intros s t H_s gcfree H_col n2 acces_t_n2.
apply (gcfree_blacks_blackt s t); auto.
apply H_s.
elim gcfree; clear gcfree.
intros ctls ctlt H_col2 heap m mksm mark n1; auto.
apply (gcfree_accest_access s t); assumption.
Qed.

Lemma nogrey_accn_imp_blackn_gcfree1 :
 forall s t : state,
 sweep_no_greys s ->
 nogrey_accn_imp_blackn s -> gc_free1 s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *; unfold sweep_no_greys in |- *.
intros s t inv4_s H_s gcfree1 H_col n2 acces_t_n2.
apply (gcfree1_blacks_blackt s t); auto.
apply H_s.
intro n1; apply inv4_s.
elim gcfree1; clear gcfree1; auto.
apply (gcfree1_accest_access s t); assumption.
Qed.

Lemma nogrey_accn_imp_blackn_gcend :
 forall s t : state,
 nogrey_accn_imp_blackn s -> gc_end s t -> nogrey_accn_imp_blackn t.

unfold nogrey_accn_imp_blackn in |- *.
intros s t H_s gcend H_col n2 acces_t_n2.
apply (gcend_blacks_blackt s t); auto.
apply H_s.
intro n1; apply (gcend_notgreyt_notgreys s t); auto.
apply (gcend_accest_access s t); auto.
Qed.

End invariant5.

Hint Immediate nogrey_accn_imp_blackn_addedge.
Hint Immediate nogrey_accn_imp_blackn_removeedge.
Hint Immediate nogrey_accn_imp_blackn_alloc.
Hint Immediate nogrey_accn_imp_blackn_gccall.
Hint Immediate nogrey_accn_imp_blackn_marknode.
Hint Immediate nogrey_accn_imp_blackn_gcstop.
Hint Immediate nogrey_accn_imp_blackn_gcfree.
Hint Immediate nogrey_accn_imp_blackn_gcfree1.
Hint Immediate nogrey_accn_imp_blackn_gcend.
Hint Immediate imp1.




