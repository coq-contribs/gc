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
(*                              accnotfree.v                                *)
(****************************************************************************)

Section invariant4.

Require Export lemma_step.
Require Export sweepnogrey.
Require Export rtgreyorblack.

Lemma acc_imp_notfree_init :
 forall s : state, init_state s -> acc_imp_notfree s.

unfold acc_imp_notfree in |- *.
intros s init n acces_s_n.
elim acces_s_n; clear acces_s_n.
cut (rt_grey_or_black s); unfold rt_grey_or_black in |- *.
intro mksrt; elim mksrt; clear mksrt.
intro mksrt; rewrite mksrt; discriminate.
intro mksrt; rewrite mksrt; discriminate.
apply (rt_grey_or_black_init s); assumption.
intros n0 m acces_s_m mksm hsmn0; elim init; clear init.
intros ctls H_mark_col; elim H_mark_col; clear H_mark_col.
intros init heap; absurd (hp s m n0 = false); auto.
rewrite hsmn0; discriminate.
Qed.


Lemma acc_imp_notfree_addedge :
 forall s t : state, acc_imp_notfree s -> add_edge s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
intros s t H_s addedge n acces_t_n.
apply (add_notfrees_notfreet s t); auto.
apply H_s; apply (add_accest_access s t); assumption.
Qed.

Lemma acc_imp_notfree_removeedge :
 forall s t : state,
 acc_imp_notfree s -> remove_edge s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
intros s t H_s removeedge n acces_t_n.
apply (remove_notfrees_notfreet s t); auto.
apply H_s; apply (remove_accest_access s t); assumption.
Qed.

Lemma acc_imp_notfree_alloc :
 forall s t : state, acc_imp_notfree s -> alloc s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
intros s t H_s alloc n acces_t_n.
elim alloc; clear alloc.
intros ctls ctlt n0 mksn0 H_fils mark add; elim mark; clear mark.
intros mark mktn0; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; rewrite mktn0; discriminate.
intro ndifn0.
rewrite <- (mark n ndifn0).
apply H_s; apply (alloc_accest_access s t n0); auto.
unfold update_color in |- *; auto.
Qed.

Lemma acc_imp_notfree_gccall :
 forall s t : state,
 nogrey_accn_imp_blackn s ->
 acc_imp_notfree s -> gc_call s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
intros s t inv5_s H_s gccall.
elim gccall; clear gccall.
intros ctls ctlt heap H_col init n acces_t_n.
apply (initcolor_notfrees_notfreet s t); auto.
apply H_s; rewrite <- heap; assumption.
intros ctls ctlt heap H_sons n acces_t_n.
apply (greynode_notfrees_notfreet s t n); auto.
apply H_s; elim H_sons; clear H_sons.
intros g mksg mktg H_col1 H_col2; rewrite <- heap; assumption.
intros ctls ctlt heap H_col m mksm mark n acces_t_n.
elim mark; clear mark.
intros mark mktm.
unfold nogrey_accn_imp_blackn in inv5_s.
rewrite <- (mark n).
rewrite inv5_s; auto.
discriminate.
rewrite heap; assumption.
apply (noteqmar_noteqnod (mk s) n m); rewrite mksm; rewrite inv5_s; auto.
discriminate.
rewrite heap; assumption.
Qed.

Lemma acc_imp_notfree_marknode :
 forall s t : state, acc_imp_notfree s -> mark_node s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
intros s t H_s marknode n acces_t_n.
apply (marknode_notfrees_notfreet s t); auto.
apply H_s; apply (marknode_accest_access s t); assumption.
Qed.

Lemma acc_imp_notfree_gcstop :
 forall s t : state, acc_imp_notfree s -> gc_stop s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
intros s t H_s gcstop n acces_t_n.
apply (gcstop_notfrees_notfreet s t); auto.
apply H_s; apply (gcstop_accest_access s t); assumption.
Qed.

Lemma acc_imp_notfree_gcfree :
 forall s t : state,
 nogrey_accn_imp_blackn s ->
 acc_imp_notfree s -> gc_free s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
unfold nogrey_accn_imp_blackn in |- *.
intros s t inv5_s H_s gcfree n acces_t_n.
elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm mark; elim mark; clear mark.
intros mark mktm; rewrite <- (mark n).
rewrite inv5_s; auto.
discriminate.
rewrite <- heap; assumption.
apply (noteqmar_noteqnod (mk s) n m); rewrite mksm; rewrite inv5_s; auto.
discriminate.
rewrite <- heap; assumption.
Qed.

Lemma acc_imp_notfree_gcfree1 :
 forall s t : state,
 sweep_no_greys s ->
 nogrey_accn_imp_blackn s ->
 acc_imp_notfree s -> gc_free1 s t -> acc_imp_notfree t.

unfold nogrey_accn_imp_blackn in |- *.
unfold sweep_no_greys in |- *.
unfold acc_imp_notfree in |- *.
intros s t inv4_s inv5_s H_s gcfree1 n acces_t_n.
elim gcfree1; clear gcfree1.
intros ctls ctlt heap n0 mksn0 mark; elim mark; clear mark.
intros mark mktn0; rewrite <- (mark n).
rewrite inv5_s; auto.
discriminate.
rewrite heap; assumption.
apply (noteqmar_noteqnod (mk s) n n0); rewrite mksn0; rewrite inv5_s; auto.
discriminate.
rewrite heap; assumption.
Qed.

Lemma acc_imp_notfree_gcend :
 forall s t : state, acc_imp_notfree s -> gc_end s t -> acc_imp_notfree t.

unfold acc_imp_notfree in |- *.
intros s t H_s gcend n acces_t_n.
apply (gcend_notfrees_notfreet s t); auto.
apply H_s; apply (gcend_accest_access s t); assumption.
Qed.

End invariant4.

Hint Immediate acc_imp_notfree_addedge.
Hint Immediate acc_imp_notfree_removeedge.
Hint Immediate acc_imp_notfree_alloc.
Hint Immediate acc_imp_notfree_gccall.
Hint Immediate acc_imp_notfree_marknode.
Hint Immediate acc_imp_notfree_gcstop.
Hint Immediate acc_imp_notfree_gcfree.
Hint Immediate acc_imp_notfree_gcfree1.
Hint Immediate acc_imp_notfree_gcend.

