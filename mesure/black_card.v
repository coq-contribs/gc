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
(*                              black_card.v                                *)
(****************************************************************************)

Section black_card.

Require Export card_facts.
Require Export parameters_card.
Require Export lemme_arith.
Require Export lemma_step.
Require Export Arith.
Require Export Peano_dec.
Require Export Bool.
Require Export Ensembles.

Notation Card := (card _ _) (only parsing).

(***
Lemma init_black:(s:state)
                 (init_state s)->
                 (cardinal [n:node](mk s n)=black (1)).

Intros s init;Elim init;Clear init.
Intros ctls init;Elim init;Clear init.
Intros mark heap;Elim mark;Clear mark.
Intros mksrt mark;Elim (exist_updated node color grey (mk s) rt).
Intros mk' mark';Elim mark';Clear mark'.
Intros mark' mk'rt;Unfold card_color;Apply card_S with M1:=mk' a0:=rt;Auto.
Constructor.
Intro n;Elim (eq_dec_node n rt).
Intro neqrt;Rewrite neqrt;Rewrite mk'rt;Discriminate.
Intro ndifrt;Rewrite <- (mark' n ndifrt);Rewrite (mark n ndifrt);Discriminate.
Symmetry;Apply mark';Assumption.
Rewrite mk'rt;Discriminate.
Save.
***)

Lemma init_black :
 forall s : state, init_state s -> card_color black (mk s) 1.

intros s init; elim init; clear init.
intros ctls init; elim init; clear init.
intros mark heap; elim mark; clear mark.
intros mksrt mark; elim (exist_updated node color grey (mk s) rt).
intros mk' mark'; elim mark'; clear mark'.
intros mark' mk'rt; unfold card_color in |- *;
 apply card_S with (M1 := mk') (a0 := rt); auto.
constructor.
intro n; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; rewrite mk'rt; discriminate.
intro ndifrt; rewrite <- (mark' n ndifrt); rewrite (mark n ndifrt);
 discriminate.
symmetry  in |- *; apply mark'; assumption.
rewrite mk'rt; discriminate.
Qed.

Hint Immediate init_black.


Lemma ex_init_black :
 forall s : state, init_state s -> exists b : nat, card_color black (mk s) b.

intros s init; exists 1; eauto.
Qed.

Lemma add_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b -> add_edge s t -> card_color black (mk t) b.

intros s t b card_s addedge; elim addedge; clear addedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark.
elim mark; clear mark.
intro cas1; elim cas1; clear cas1.
intros mksn1 mark; rewrite mark; assumption.
intros cas; elim cas; clear cas.
intro cas2; elim cas2; clear cas2.
intros mksn1 mark; elim mark; clear mark.
intros mksn2 mark; rewrite mark; assumption.
intro cas3; elim cas3; clear cas3.
intros mksn1 mark; elim mark; clear mark.
intros mksn2 upd_col; elim upd_col; clear upd_col.
intros mark mktn2; unfold card_color in |- *.
apply card_inv with (M1 := mk s); auto.
intros n mksn; elim (eq_dec_node n n2).
intro neqn2; rewrite neqn2; rewrite mktn2; discriminate.
intro ndifn2; rewrite <- (mark n ndifn2); assumption.
intros n mksn; rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n n2); rewrite mksn; rewrite mksn2;
 discriminate.
Qed.

Hint Resolve add_black.

Lemma ex_add_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 add_edge s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s addedge; elim card_s; clear card_s.
intros b card_s; exists b; eauto.
Qed.


Lemma remove_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b -> remove_edge s t -> card_color black (mk t) b.

intros s t b card_s removeedge.
elim removeedge; clear removeedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt remove mark.
rewrite mark; assumption.
Qed.

Hint Resolve remove_black.

Lemma ex_remove_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 remove_edge s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s removeedge; elim card_s; clear card_s.
intros b card_s; exists b; eauto.
Qed.


Lemma alloc_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b -> alloc s t -> card_color black (mk t) (S b).

intros s t b card_s alloc; elim alloc; clear alloc.
intros ctls ctlt n mksn H_fils upd_col add.
elim upd_col; clear upd_col.
intros mark mktn; unfold card_color in |- *.
apply card_S with (M1 := mk s) (a0 := n); auto.
rewrite mksn; discriminate.
Qed.

Hint Resolve alloc_black.


Lemma ex_alloc_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 alloc s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s alloc; elim card_s; clear card_s.
intros b card_s; exists (S b); eauto.
Qed.

Lemma greynode_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b ->
 grey_node_case (mk s) (mk t) (hp s) -> card_color black (mk t) (S b).

intros s t b card_s H_grey; elim H_grey; clear H_grey.
intros g mksg mktg H_mark1 H_mark2.
elim (exist_updated node color (mk s g) (mk t) g).
intros mk' mark; elim mark; clear mark.
intros mark' mk'g.
unfold card_color in |- *; apply card_S with (M1 := mk') (a0 := g); auto.
apply card_inv with (M1 := mk s); auto.
intros n mksn; elim (eq_dec_node n g).
intro neqg; rewrite neqg; rewrite mk'g; rewrite mksg; discriminate.
intros ndifg; elim (sumbool_of_bool (hp s g n)); intro hsgn.
elim (eq_dec_color (mk s n) white); intro mksn2.
rewrite <- (mark' n ndifg); rewrite (H_mark1 n); auto.
discriminate.
rewrite <- (mark' n ndifg); rewrite <- (H_mark2 n); auto.
rewrite <- (mark' n ndifg); rewrite <- (H_mark2 n); auto.
intros n mksn; elim (eq_dec_node n g).
intro neqg; rewrite neqg in mksn; absurd (mk s g = grey); auto.
rewrite mksn; discriminate.
intros ndifg; elim (sumbool_of_bool (hp s g n)); intro hsgn.
rewrite <- (mark' n ndifg).
rewrite <- (H_mark2 n); auto.
split; auto.
left; split; auto.
rewrite mksn; discriminate.
rewrite <- (mark' n ndifg); rewrite <- (H_mark2 n); auto.
symmetry  in |- *; apply mark'; assumption.
rewrite mk'g; rewrite mksg; discriminate.
Qed.

Hint Resolve greynode_black.

Lemma initcol_black :
 forall s t : state, init_color (mk s) (mk t) -> card_color black (mk t) 0.

intros s t init; elim init; clear init.
intros mktrt mark; elim mark; clear mark.
intros mark1 mark2; constructor.
intro n; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; rewrite mktrt; discriminate.
intro ndifrt; elim (eq_dec_color (mk s n) black); intro mksn.
rewrite (mark1 n ndifrt); auto.
discriminate.
rewrite (mark2 n ndifrt); auto.
Qed.

Hint Resolve initcol_black.


Lemma ex_gccall_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 gc_call s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s gccall; elim card_s; clear card_s.
intros b card_s; elim gccall; clear gccall.
intros ctls ctlt heap H_col init; exists 0; eauto.
intros ctls ctlt heap H_grey; exists (S b); eauto.
intros ctls ctlt heap H_col m mksm upd_col.
elim upd_col; clear upd_col.
intros mark mktm; exists b; unfold card_color in |- *.
apply card_inv with (M1 := mk s); auto.
intros n mksn; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n ndifm); assumption.
intros n mksn; elim (eq_dec_node n m).
intro neqm; rewrite neqm in mksn; absurd (mk s m = white); auto.
rewrite mksn; discriminate.
intro ndifm; rewrite <- (mark n ndifm); assumption.
Qed.


Lemma ex_marknode_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 mark_node s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s marknode; elim marknode; clear marknode.
intros ctls ctlt heap H_grey; elim card_s; clear card_s.
intros b card_s; exists (S b); eauto.
Qed.


Lemma gcstop_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b -> gc_stop s t -> card_color black (mk t) b.

intros s t b card_s gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcstop_black.

Lemma ex_gcstop_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 gc_stop s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s gcstop; elim card_s; clear card_s.
intros b card_s; exists b; eauto.
Qed.


Lemma gcfree_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b -> gc_free s t -> card_color black (mk t) b.

intros s t b card_s gcfree; unfold card_color in |- *.
apply card_inv with (M1 := mk s); auto.
intros n mksn; apply (gcfree_notblacks_notblackt s t); assumption.
intros n mksn; apply (gcfree_blacks_blackt s t); assumption.
Qed.

Hint Resolve gcfree_black.

Lemma ex_gcfree_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 gc_free s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s gcfree; elim card_s; clear card_s.
intros b card_s; exists b; eauto.
Qed.


Lemma gcfree1_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b -> gc_free1 s t -> card_color black (mk t) b.

intros s t b card_s gcfree1; unfold card_color in |- *.
apply card_inv with (M1 := mk s); auto.
intros n mksn; apply (gcfree1_notblacks_notblackt s t); assumption.
intros n mksn; apply (gcfree1_blacks_blackt s t); assumption.
Qed.

Hint Resolve gcfree1_black.

Lemma ex_gcfree1_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 gc_free1 s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s gcfree1; elim card_s; clear card_s.
intros b card_s; exists b; eauto.
Qed.


Lemma gcend_black :
 forall (s t : state) (b : nat),
 card_color black (mk s) b -> gc_end s t -> card_color black (mk t) b.

intros s t b card_s gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcend_black.

Lemma ex_gcend_black :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 gc_end s t -> exists b : nat, card_color black (mk t) b.

intros s t card_s gcend; elim card_s; clear card_s.
intros b card_s; exists b; eauto.
Qed.


End black_card.

Hint Immediate ex_init_black.
Hint Immediate ex_add_black.
Hint Immediate ex_remove_black.
Hint Immediate ex_alloc_black.
Hint Immediate ex_gccall_black.
Hint Immediate ex_marknode_black.
Hint Immediate ex_gcstop_black.
Hint Immediate ex_gcfree_black.
Hint Immediate ex_gcfree1_black.
Hint Immediate ex_gcend_black.
