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
(*                             sweepnogrey.v                                *)
(****************************************************************************)

Section invariant2.

Require Export gc.

Lemma absurd :
 forall c c1 c2 : control, c = c1 -> c = c2 -> c1 <> c2 -> False.

intros c c1 c2 ceqc1 ceqc2 c1difc2; absurd (c = c1); auto.
rewrite ceqc2; auto.
Qed.


Lemma sweep_no_greys_init :
 forall s : state, init_state s -> sweep_no_greys s.

unfold init_state in |- *; unfold sweep_no_greys in |- *.
intros s init ctls n.
elim init; clear init.
intros ctls2 init.
absurd (ctl s = sweep); auto.
rewrite ctls2; discriminate.
Qed.


Lemma sweep_no_greys_addedge :
 forall s t : state, sweep_no_greys s -> add_edge s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *.
intros s t H_s addedge ctlt n.
elim addedge; clear addedge.
intros n0 m acces_s_n0 acces_s_m ctls ctlt2 add mark.
absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
Qed.

Lemma sweep_no_greys_removeedge :
 forall s t : state, sweep_no_greys s -> remove_edge s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s removeedge ctlt n.
elim removeedge; clear removeedge.
intros n0 m acces_s_n0 acces_s_m ctls ctlt2 remove mark.
absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
Qed.

Lemma sweep_no_greys_alloc :
 forall s t : state, sweep_no_greys s -> alloc s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s alloc ctlt n.
elim alloc; clear alloc.
intros ctls ctlt2 n0 mksn0 H_fils upd_col add.
absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
Qed.

Lemma sweep_no_greys_gccall :
 forall s t : state, sweep_no_greys s -> gc_call s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s gccall ctlt n.
elim gccall; clear gccall.
intros ctls ctlt2 heap H_col init; absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
intros ctls ctlt2 heap H_sons; absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
intros ctls ctlt2 heap H_col m mksm upd_col.
absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
Qed.

Lemma sweep_no_greys_marknode :
 forall s t : state, sweep_no_greys s -> mark_node s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s marknode ctlt n.
elim marknode; clear marknode.
intros ctls ctlt2 heap H_sons; absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
Qed.

Lemma sweep_no_greys_gcstop :
 forall s t : state, sweep_no_greys s -> gc_stop s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s gcstop ctlt n.
elim gcstop; clear gcstop.
intros ctls ctlt2 heap mark; absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
Qed.

Lemma sweep_no_greys_gcfree :
 forall s t : state, sweep_no_greys s -> gc_free s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s gcfree ctlt n.
elim gcfree; clear gcfree.
intros ctls ctlt2 H_col heap m mksm mark.
elim mark; clear mark.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n ndifm); auto.
Qed.

Lemma sweep_no_greys_gcfree1 :
 forall s t : state, sweep_no_greys s -> gc_free1 s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s gcfree1 ctlt n.
elim gcfree1; clear gcfree1.
intros ctls ctlt2 heap n0 mksn0 mark; elim mark; clear mark.
intros mark mktn0; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; rewrite mktn0; discriminate.
intro ndifn0; rewrite <- (mark n ndifn0); apply H_s; assumption.
Qed.

Lemma sweep_no_greys_gcend :
 forall s t : state, sweep_no_greys s -> gc_end s t -> sweep_no_greys t.

unfold sweep_no_greys in |- *; intros s t H_s gcend ctlt n.
elim gcend; clear gcend.
intros ctls ctlt2 heap mark; absurd (ctl t = sweep); auto.
rewrite ctlt2; discriminate.
Qed.

End invariant2.

Hint Immediate sweep_no_greys_addedge.
Hint Immediate sweep_no_greys_removeedge.
Hint Immediate sweep_no_greys_alloc.
Hint Immediate sweep_no_greys_gccall.
Hint Immediate sweep_no_greys_marknode.
Hint Immediate sweep_no_greys_gcstop.
Hint Immediate sweep_no_greys_gcfree.
Hint Immediate sweep_no_greys_gcfree1.
Hint Immediate sweep_no_greys_gcend.
