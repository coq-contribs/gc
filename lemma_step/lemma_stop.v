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
(*                              lemma_stop.v                                *)
(****************************************************************************)

Section lemma_stop.

Require Export gc.
Require Export reachable.

Notation Reachable := (reachable node) (only parsing).

Lemma gcstop_accest_access :
 forall s t : state,
 gc_stop s t ->
 forall n : node, accessible node (hp t) rt n -> accessible node (hp s) rt n.

intros s t gcstop n acces_t_n; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite <- heap; assumption.
Qed.

Lemma gcstop_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 gc_stop s t -> ~ accessible node (hp t) rt n.

intros s t n notacces_n_s gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite heap; assumption.
Qed.

Lemma gcstop_ancestor_col :
 forall (s t : state) (n : node),
 (forall m : node,
  reachable node (hp s) m n -> mk s m = white \/ mk s m = free) ->
 gc_stop s t ->
 forall m : node,
 reachable node (hp t) m n -> mk t m = white \/ mk t m = free.

intros s t n H_reach gcstop m H_reach_m_t; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; apply H_reach; rewrite <- heap;
 assumption.
Qed.

Lemma gcstop_blacks_blackt :
 forall s t : state,
 gc_stop s t -> forall n : node, mk s n = black -> mk t n = black.

intros s t gcstop n acces_t_n; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Lemma gcstop_notgreyt_notgreys :
 forall s t : state,
 gc_stop s t -> forall n : node, mk t n <> grey -> mk s n <> grey.

intros s t gcstop n acces_t_n; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite <- mark; assumption.
Qed.

Lemma gcstop_notfrees_notfreet :
 forall s t : state,
 gc_stop s t -> forall n : node, mk s n <> free -> mk t n <> free.

intros s t gcstop n acces_t_n; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Lemma gcstop_white :
 forall (s t : state) (n : node),
 mk s n = white -> gc_stop s t -> mk t n = white.

intros s t n mksn gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Lemma gcstop_nogrey :
 forall s t : state,
 (forall n : node, mk s n <> grey) ->
 gc_stop s t -> forall n : node, mk t n <> grey.

intros s t mksn gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; auto.
Qed.

Lemma gcstop_nowhite :
 forall s t : state,
 (forall n : node, mk s n <> white) ->
 gc_stop s t -> forall n : node, mk t n <> white.

intros s t mksn gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; auto.
Qed.

End lemma_stop.

Hint Resolve gcstop_notaccess_notaccest.
Hint Resolve gcstop_white.
Hint Resolve gcstop_nogrey.
Hint Resolve gcstop_blacks_blackt.
Hint Resolve gcstop_nowhite.
Hint Resolve gcstop_ancestor_col.