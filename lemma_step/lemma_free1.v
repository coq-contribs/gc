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
(*                              lemma_free1.v                               *)
(****************************************************************************)

Section lemma_free1.

Require Export gc.

Lemma gcfree1_nowhite :
 forall s t : state,
 (forall n : node, mk s n <> white) ->
 gc_free1 s t -> forall n : node, mk t n <> white.

intros s t H_white gcfree; elim gcfree; clear gcfree.
intros ctls ctlt heap m mksm; absurd (mk s m = white); auto.
Qed.

Lemma gcfree1_nogrey :
 forall s t : state,
 (forall n : node, mk s n <> grey) ->
 gc_free1 s t -> forall n : node, mk t n <> grey.

intros s t H_grey gcfree1; elim gcfree1; clear gcfree1.
intros ctls ctlt heap m mksm H; elim H; clear H.
intros mark mktm n; elim (eq_dec_node n m).
intro neqm; rewrite neqm; intro mktn; absurd (mk t m = free); auto.
rewrite mktn; discriminate.
intro ndifm; rewrite <- (mark n ndifm); auto.
Qed.


Lemma gcfree1_accest_access :
 forall s t : state,
 gc_free1 s t ->
 forall n : node, accessible node (hp t) rt n -> accessible node (hp s) rt n.

intros s t gcfree1 n acces_t_n; elim gcfree1; clear gcfree1.
intros ctls ctlt heap n0 mksn0 mark; rewrite heap; assumption.
Qed.

Lemma gcfree1_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 gc_free1 s t -> ~ accessible node (hp t) rt n.

intros s t n notacess_n_s gcfree1; elim gcfree1; clear gcfree1.
intros ctls ctlt heap n0 mksn0 upd_col; rewrite <- heap; assumption.
Qed.

Lemma gcfree1_blacks_blackt :
 forall s t : state,
 gc_free1 s t -> forall n : node, mk s n = black -> mk t n = black.

intros s t gcfree1 n mksn; elim gcfree1; clear gcfree1.
intros ctls ctlt heap n0 mksn0 mark; elim mark; clear mark.
intros mark mktn0; rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n n0); rewrite mksn; rewrite mksn0;
 discriminate.
Qed.

Lemma gcfree1_notblacks_notblackt :
 forall s t : state,
 gc_free1 s t -> forall n : node, mk s n <> black -> mk t n <> black.

intros s t gcfree1 n mksn; elim gcfree1; clear gcfree1.
intros ctls ctlt heap m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n ndifm); assumption.
Qed.

Lemma gcfree1_greys_greyt :
 forall s t : state,
 gc_free1 s t -> forall n : node, mk s n = grey -> mk t n = grey.

intros s t gcfree1 n mksn; elim gcfree1; clear gcfree1.
intros ctls ctlt heap n0 mksn0 mark; elim mark; clear mark.
intros mark mktn0; rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n n0); rewrite mksn; rewrite mksn0;
 discriminate.
Qed.

Lemma gcfree1_notgreys_notgreyt :
 forall s t : state,
 gc_free1 s t -> forall n : node, mk s n <> grey -> mk t n <> grey.

intros s t gcfree1 n mksn; elim gcfree1; clear gcfree1.
intros ctls ctlt heap n0 mksn0 mark; elim mark; clear mark.
intros mark mktn0; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; rewrite mktn0; discriminate.
intro ndifn0; rewrite <- (mark n ndifn0); assumption.
Qed.

End lemma_free1.

Hint Resolve gcfree1_notaccess_notaccest.
Hint Resolve gcfree1_notgreys_notgreyt.
Hint Resolve gcfree1_blacks_blackt.
Hint Resolve gcfree1_nowhite.
Hint Resolve gcfree1_nogrey.