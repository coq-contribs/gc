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
(*                              reachable.v                                 *)
(****************************************************************************)

Section reachable.

Variables (N : Set) (h : N -> N -> bool) (root : N).

Inductive reachable (s : N) : N -> Prop :=
  | reachable_init : reachable s s
  | reachable_edge :
      forall n m : N, reachable s m -> h m n = true -> reachable s n.

Definition accessible (n : N) : Prop := reachable root n.

Lemma reach_acc :
 forall ancestor n : N,
 reachable ancestor n -> accessible ancestor -> accessible n.

unfold accessible in |- *; intros ancestor n H_reach H_acc.
elim H_reach; try assumption.
clear H_reach H_acc n; intros n m H_reach H_ind H_fils.
apply reachable_edge with (m := m); assumption.
Qed.

Hint Resolve reach_acc.

Lemma reach_notacc :
 forall ancestor n : N,
 reachable ancestor n -> ~ accessible n -> ~ accessible ancestor.

intros ancestor n H_ancestor H_not_acc; intro H_acc.
apply H_not_acc; eauto.
Qed.

Lemma reach_true_reach :
 forall s n m : N, reachable m n -> h s m = true -> reachable s n.

intros s n m H_reach; elim H_reach.
intro hsm; apply reachable_edge with (m := s); auto.
constructor.
clear H_reach n.
intros n' m' H_reach H_ind hm'n' hsm.
apply reachable_edge with (m := m'); auto.
Qed.

End reachable.


