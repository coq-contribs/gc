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
(*                               lemma_end.v                                *)
(****************************************************************************)

Section lemma_end.

Require Export gc.
Require Export reachable.

Notation Reachable := (reachable node) (only parsing).

Lemma gcend_ancestor_col :
 forall (s t : state) (n : node),
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 gc_end s t ->
 forall m : node,
 reachable node (hp t) m n -> mk t m = white \/ mk t m = free.

intros s t n H_reach gcend m H_reach_m_t; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; apply H_reach; rewrite <- heap;
 assumption.
Qed.

Lemma gcend_accest_access :
 forall s t : state,
 gc_end s t ->
 forall n : node, accessible node (hp t) rt n -> accessible node (hp s) rt n.

intros s t gcend n acces_t_n; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite <- heap; assumption.
Qed.

Lemma gcend_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n -> gc_end s t -> ~ accessible node (hp t) rt n.

intros s t n notacces_n_s gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite heap; assumption.
Qed.

Lemma gcend_notgreyt_notgreys :
 forall s t : state,
 gc_end s t -> forall n : node, mk t n <> grey -> mk s n <> grey.

intros s t gcend n mktn; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite <- mark; assumption.
Qed.

Lemma gcend_blacks_blackt :
 forall s t : state,
 gc_end s t -> forall n : node, mk s n = black -> mk t n = black.

intros s t gcend n mktn; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Lemma gcend_notfrees_notfreet :
 forall s t : state,
 gc_end s t -> forall n : node, mk s n <> free -> mk t n <> free.

intros s t gcend n mktn; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Lemma gcend_white :
 forall (s t : state) (n : node),
 mk s n = white -> gc_end s t -> mk t n = white.

intros s t n mksn gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Lemma gcend_nogrey :
 forall s t : state,
 (forall n : node, mk s n <> grey) ->
 gc_end s t -> forall n : node, mk t n <> grey.

intros s t mksn gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; auto.
Qed.

Lemma gcend_nowhite :
 forall s t : state,
 (forall n : node, mk s n <> white) ->
 gc_end s t -> forall n : node, mk t n <> white.

intros s t mksn gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; auto.
Qed.

End lemma_end.

Hint Resolve gcend_notaccess_notaccest.
Hint Resolve gcend_white.
Hint Resolve gcend_nowhite.
Hint Resolve gcend_blacks_blackt.
Hint Resolve gcend_nogrey.
Hint Resolve gcend_ancestor_col.