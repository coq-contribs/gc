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
(*                             rtgreyorblack.v                              *)
(****************************************************************************)

Section invariant1.

Require Export gc.
Require Export Sumbool.

Lemma rt_grey_or_black_init :
 forall s : state, init_state s -> rt_grey_or_black s.

unfold rt_grey_or_black in |- *; unfold init_state in |- *; intros s init;
 right.
elim init; clear init.
intros ctls init; elim init; clear init; unfold init_marking in |- *.
intros mark heap; elim mark; clear mark.
intros mksrt mark; assumption.
Qed.


Lemma rt_grey_or_black_addedge :
 forall s t : state, rt_grey_or_black s -> add_edge s t -> rt_grey_or_black t.

unfold rt_grey_or_black in |- *; intros s t H_s addedge.
elim addedge; clear addedge; unfold marking_add in |- *.
intros n m acces_s_n acces_s_m ctls ctlt add mark.
elim mark; clear mark.
intro case1; elim case1; clear case1.
intros mksn mark; rewrite mark; assumption.
intros case; elim case; clear case.
intro case2; elim case2; clear case2.
intros mksn mark; elim mark; clear mark.
intros mksm mark; rewrite mark; assumption.
intros case3; elim case3; clear case3.
intros mksn mark; elim mark; clear mark.
intros mksm mark; elim mark; clear mark.
intros mark mktm; unfold rt_grey_or_black in |- *;
 unfold rt_grey_or_black in H_s.
elim H_s; clear H_s.
intro mksrt; left; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt m); rewrite mksrt; rewrite mksm;
 discriminate.
intro mksrt; right; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt m); rewrite mksrt; rewrite mksm;
 discriminate.
Qed.

Lemma rt_grey_or_black_removeedge :
 forall s t : state,
 rt_grey_or_black s -> remove_edge s t -> rt_grey_or_black t.

unfold rt_grey_or_black in |- *; intros s t H_s removeedge.
elim removeedge; clear removeedge.
intros n m acces_s_n acces_s_m ctls ctlt remove mark.
rewrite mark; assumption.
Qed.

Lemma rt_grey_or_black_alloc :
 forall s t : state, rt_grey_or_black s -> alloc s t -> rt_grey_or_black t.

unfold rt_grey_or_black in |- *; intros s t H_s alloc.
elim alloc; clear alloc.
intros ctls ctlt n mksn H_fils mark add.
elim mark; clear mark.
intros mark mktn.
elim H_s; clear H_s.
intro mksrt; left; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt n); rewrite mksrt; rewrite mksn;
 discriminate.
intro mksrt; right; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt n); rewrite mksrt; rewrite mksn;
 discriminate.
Qed.

Lemma black_grey_node :
 forall s t : state,
 rt_grey_or_black s ->
 grey_node_case (mk s) (mk t) (hp s) -> rt_grey_or_black t.

unfold rt_grey_or_black in |- *; intros s t H_s H_sons.
elim H_sons; clear H_sons.
intros g mksg mktg case1 case2.
elim (eq_dec_node rt g).
intro rteqg; right; rewrite rteqg; assumption.
intro rtdifg; elim H_s; clear H_s.
intro mksrt; elim (sumbool_of_bool (hp s g rt)); intro hsgrt.
left; rewrite <- (case2 rt); auto.
split; auto.
left; split; auto.
rewrite mksrt; discriminate.
left; rewrite <- (case2 rt); auto.
right; auto.
elim (sumbool_of_bool (hp s g rt)); intro hsgrt.
rewrite <- (case2 rt); auto.
split; auto.
left; split; auto.
rewrite H; discriminate.
rewrite <- (case2 rt); auto.
Qed.


Lemma free_white_node :
 forall (s t : state) (n : node),
 rt_grey_or_black s ->
 mk s n = white -> update_color (mk s) (mk t) free n -> rt_grey_or_black t.

unfold rt_grey_or_black in |- *; intros s t n H_s mksn mark; elim mark;
 clear mark.
intros mark mktn; elim H_s; clear H_s.
intro mksrt; left; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt n); rewrite mksrt; rewrite mksn;
 discriminate.
intro mksrt; right; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt n); rewrite mksrt; rewrite mksn;
 discriminate.
Qed.


Lemma rt_grey_or_black_gccall :
 forall s t : state, rt_grey_or_black s -> gc_call s t -> rt_grey_or_black t.

intros s t H_s gccall; elim gccall; clear gccall; unfold init_color in |- *.
intros ctls ctlt heap mark init; elim init; clear init.
intros mktrt mark_case; unfold rt_grey_or_black in |- *; left; assumption.
intros ctls ctlt heap H_sons; apply (black_grey_node s t); auto.
intros ctls ctlt heap mark m mksm upd_col.
apply (free_white_node s t m); assumption.
Qed.

Lemma rt_grey_or_black_marknode :
 forall s t : state,
 rt_grey_or_black s -> mark_node s t -> rt_grey_or_black t.

intros s t H_s marknode; elim marknode; clear marknode.
intros ctls ctlt heap H_sons; apply (black_grey_node s t); assumption.
Qed.

Lemma rt_grey_or_black_gcstop :
 forall s t : state, rt_grey_or_black s -> gc_stop s t -> rt_grey_or_black t.

unfold rt_grey_or_black in |- *; intros s t H_s gcstop; elim gcstop;
 clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Lemma rt_grey_or_black_gcfree :
 forall s t : state, rt_grey_or_black s -> gc_free s t -> rt_grey_or_black t.

unfold rt_grey_or_black in |- *; intros s t H_s gcfree; elim gcfree;
 clear gcfree.
intros ctls ctlt H_col heap m mksm mark; elim mark; clear mark.
intros mark mktm.
unfold rt_grey_or_black in |- *; unfold rt_grey_or_black in H_s.
elim H_s; clear H_s.
intro mksrt; left; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt m); rewrite mksrt; rewrite mksm;
 discriminate.
intro mksrt; right; rewrite <- (mark rt); auto.
apply (noteqmar_noteqnod (mk s) rt m); rewrite mksrt; rewrite mksm;
 discriminate.
Qed.

Lemma rt_grey_or_black_gcfree1 :
 forall s t : state, rt_grey_or_black s -> gc_free1 s t -> rt_grey_or_black t.

intros s t H_s gcfree1.
elim gcfree1; clear gcfree1.
intros ctls ctlt heap n mksn upd_col.
apply (free_white_node s t n); assumption.
Qed.

Lemma rt_grey_or_black_gcend :
 forall s t : state, rt_grey_or_black s -> gc_end s t -> rt_grey_or_black t.


unfold rt_grey_or_black in |- *; intros s t H_s gcend.
elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

End invariant1.

Hint Resolve rt_grey_or_black_init.
Hint Immediate rt_grey_or_black_addedge.
Hint Immediate rt_grey_or_black_removeedge.
Hint Immediate rt_grey_or_black_alloc.
Hint Immediate rt_grey_or_black_gccall.
Hint Immediate rt_grey_or_black_marknode.
Hint Immediate rt_grey_or_black_gcstop.
Hint Immediate rt_grey_or_black_gcfree.
Hint Immediate rt_grey_or_black_gcfree1.
Hint Immediate rt_grey_or_black_gcend.