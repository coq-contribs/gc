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
(*                               lemma_free.v                               *)
(****************************************************************************)

Section lemma_free.

Require Export gc.

Lemma gcfree_nowhite :
 forall s t : state,
 (forall n : node, mk s n <> white) ->
 gc_free s t -> forall n : node, mk t n <> white.

intros s t H_white gcfree; elim gcfree; clear gcfree.
intros ctls ctlt H_grey heap m mksm; absurd (mk s m = white); auto.
Qed.

Lemma gcfree_nogrey :
 forall s t : state,
 (forall n : node, mk s n <> grey) ->
 gc_free s t -> forall n : node, mk t n <> grey.

intros s t H_grey gcfree; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm H; elim H; clear H.
intros mark mktm n; elim (eq_dec_node n m).
intro neqm; rewrite neqm; intro mktn; absurd (mk t m = free); auto.
rewrite mktn; discriminate.
intro ndifm; rewrite <- (mark n ndifm); auto.
Qed.

Lemma updatecolor_blacks_blackt :
 forall s t : state,
 (forall n : node, mk s n <> grey) ->
 forall m : node,
 mk s m = white ->
 update_color (mk s) (mk t) free m ->
 forall n : node, mk s n = black -> mk t n = black.

intros s t H_col m mksm mark n mksn; elim mark; clear mark.
intros mark mktm; rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n m); rewrite mksn; rewrite mksm;
 discriminate.
Qed.

Lemma gcfree_blacks_blackt :
 forall s t : state,
 gc_free s t -> forall n : node, mk s n = black -> mk t n = black.

intros s t gcfree n mksn; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm mark;
 apply (updatecolor_blacks_blackt s t) with (m := m); 
 auto.
Qed.

Lemma gcfree_notblacks_notblackt :
 forall s t : state,
 gc_free s t -> forall n : node, mk s n <> black -> mk t n <> black.

intros s t gcfree n mksn; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n ndifm); assumption.
Qed.

Lemma gcfree_accest_access :
 forall s t : state,
 gc_free s t ->
 forall n : node, accessible node (hp t) rt n -> accessible node (hp s) rt n.

intros s t gcfree n acces_t_n; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm mark; rewrite <- heap; assumption.
Qed.

Lemma gcfree_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 gc_free s t -> ~ accessible node (hp t) rt n.

intros s t n notacces_n_s gcfree; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm upd_col; rewrite heap; assumption.
Qed.

Lemma gcfree_notgreys_notgreyt :
 forall s t : state,
 gc_free s t -> forall n : node, mk s n <> grey -> mk t n <> grey.

intros s t gcfree n mksn; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm mark; elim mark; clear mark.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n ndifm); assumption.
Qed.

Lemma gcfree_greys_greyt :
 forall s t : state,
 gc_free s t -> forall n : node, mk s n = grey -> mk t n = grey.

intros s t gcfree n mksn; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm mark; absurd (mk s n = grey); auto.
Qed.

End lemma_free.

Hint Resolve gcfree_blacks_blackt.
Hint Resolve gcfree_notaccess_notaccest.
Hint Resolve gcfree_notgreys_notgreyt.
Hint Resolve gcfree_nowhite.
Hint Resolve gcfree_nogrey.