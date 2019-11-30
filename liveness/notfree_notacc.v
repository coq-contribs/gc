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
(*                            notfree_notacc.v                              *)
(****************************************************************************)

Section notfree_notacc.

Require Export gc.
Require Export lemma_step.
Require Import Bool.
Require Export parameters_card.

Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation State_formula := (state_formula state) (only parsing).
Notation Stream := (stream state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Trace := (trace (fun (a : label) (s t : state) => transition s t a))
  (only parsing).

Lemma addedge_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 add_edge s t -> ~ accessible node (hp t) rt n.

intros s t n H_n addedge; elim H_n; clear H_n.
intros mksn acces_n_s; apply (add_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate addedge_notacces_t.


Lemma removeedge_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 remove_edge s t -> ~ accessible node (hp t) rt n.

intros s t n H_n removeedge; elim H_n; clear H_n.
intros mksn acces_n_s; apply (remove_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate removeedge_notacces_t.


Lemma alloc_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 alloc s t -> ~ accessible node (hp t) rt n.

intros s t n H_n alloc; elim alloc; clear alloc.
intros ctls ctlt n0 mksn0 H_fils upd_col add; elim add; clear add.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htrtn0; elim H_n; clear H_n.
intros mksn notacces_n_s; intro acces_n_t.
inversion acces_n_t.
rewrite <- H in notacces_n_s; absurd (accessible node (hp s) rt rt); auto. 
constructor.
elim (eq_dec_node m rt).
intro meqrt; elim (eq_dec_node n n0). 
intro neqn0; apply mksn; rewrite <- neqn0 in mksn0; assumption.
intro ndifn0; absurd (accessible node (hp s) rt n); auto.
unfold accessible in |- *; apply reachable_edge with (m := rt).
constructor.
rewrite (H_heap2 n ndifn0); rewrite <- meqrt; assumption.
intro mdifrt; absurd (accessible node (hp s) rt n); auto.
elim (eq_dec_node m n0).
intro meqn0; elim (sumbool_of_bool (hp s n0 n)); intro hsn0n.
rewrite meqn0 in H0; absurd (hp t n0 n = true); auto.
intro htn0n; apply (eq_true_false_abs (hp t n0 n)); auto.
unfold remove in H_fils; elim (H_fils n); auto.
intros heap1 heap2; elim heap2; clear heap2; auto.
absurd (hp t m n = true); auto.
intro htn1n; apply (eq_true_false_abs (hp s n0 n)); auto.
rewrite <- meqn0; rewrite (H_heap1 m n mdifrt); assumption.
intro mdifn0; unfold accessible in |- *; apply reachable_edge with (m := m).
replace (reachable node (hp s) rt m) with (accessible node (hp s) rt m); auto.
apply (alloc_accest_access s t n0); auto.
unfold add in |- *; auto.
rewrite (H_heap1 m n mdifrt); assumption.
Qed.

Hint Immediate alloc_notacces_t.


Lemma gccall_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 gc_call s t -> ~ accessible node (hp t) rt n.

intros s t n H_n gccall; elim H_n; clear H_n.
intros mksn acces_n_s.
apply (gccall_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate gccall_notacces_t.

Lemma marknode_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 mark_node s t -> ~ accessible node (hp t) rt n.

intros s t n H_n marknode; elim H_n; clear H_n.
intros mksn acces_n_s.
apply (marknode_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate marknode_notacces_t.

Lemma gcstop_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 gc_stop s t -> ~ accessible node (hp t) rt n.

intros s t n H_n gcstop; elim H_n; clear H_n.
intros mksn acces_n_s.
apply (gcstop_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate gcstop_notacces_t.

Lemma gcfree_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 gc_free s t -> ~ accessible node (hp t) rt n.

intros s t n H_n gcfree; elim H_n; clear H_n.
intros mksn acces_n_s.
apply (gcfree_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate gcfree_notacces_t.

Lemma gcfree1_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 gc_free1 s t -> ~ accessible node (hp t) rt n.

intros s t n H_n gcfree1.
elim H_n; clear H_n.
intros mksn acces_n_s.
apply (gcfree1_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate gcfree1_notacces_t.

Lemma gcend_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 gc_end s t -> ~ accessible node (hp t) rt n.

intros s t n H_n gcend.
elim H_n; clear H_n.
intros mksn acces_n_s.
apply (gcend_notaccess_notaccest s t n); assumption.
Qed.

Hint Immediate gcend_notacces_t.

Lemma step_notacces_t :
 forall (s t : state) (n : node),
 mk s n <> free /\ ~ accessible node (hp s) rt n ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 ~ accessible node (hp t) rt n. 

intros s t n H_n step; elim step; intro a; case a; intro trans;
 inversion trans; eauto.
Qed.

Definition notfree_notacces (n : node) : stream_formula state :=
  state2stream_formula
    (fun s : state => mk s n <> free /\ ~ accessible node (hp s) rt n).

Definition notfree (n : node) : stream_formula state :=
  state2stream_formula (fun s : state => mk s n <> free).

Definition is_free (n : node) : stream_formula state :=
  state2stream_formula (fun s : state => mk s n = free).

Lemma notfree_notacces_unless_isfree :
 forall (str : stream state) (n : node),
 notfree_notacces n str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 unless (notfree_notacces n) (is_free n) str.

cofix notfree_notacces_unless_isfree; intros str; case str.
intros s str'; case str'.
intros t tl n H_n H_trace; elim (eq_dec_color (mk t n) free); intro mktn.
constructor 2; auto.
constructor 1; unfold is_free in |- *; unfold state2stream_formula in |- *;
 simpl in |- *; assumption.
constructor 2; auto.
apply (notfree_notacces_unless_isfree (cons_str t tl) n); auto.
unfold notfree_notacces in |- *; unfold state2stream_formula in |- *.
simpl in |- *; split; auto.
unfold trace in H_trace; inversion_clear H_trace; simpl in H.
elim H; clear H; auto.
unfold notfree_notacces in H_n; unfold state2stream_formula in H_n;
 simpl in H_n.
elim H_n; auto.
intros t0 step_s_t0.
apply (step_notacces_t s t0 n); auto.
inversion H_trace; assumption.
Qed.

Hint Resolve notfree_notacces_unless_isfree.

Lemma always_notfree_notacces_unless_isfree :
 forall (str : stream state) (n : node),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (fun str : stream state =>
    notfree_notacces n str -> unless (notfree_notacces n) (is_free n) str)
   str.

cut
 (forall (str : stream state) (n : node),
  notfree_notacces n str ->
  trace (fun (a : label) (s t : state) => transition s t a) str ->
  unless (notfree_notacces n) (is_free n) str); eauto.
intro unless_notfree_free; cofix always_notfree_notacces_unless_isfree.
intro str; case str.
intros s tl n H_trace; constructor.
intro notfree_s.
apply unless_notfree_free; assumption.
apply always_notfree_notacces_unless_isfree.
inversion H_trace; assumption.
Qed.

Definition free_or_notfree_notacc_nogrey (n : node) : 
  stream_formula state :=
  state2stream_formula
    (fun s : state =>
     mk s n = free \/
     (mk s n <> free /\ ~ accessible node (hp s) rt n) /\
     card_color grey (mk s) 0).

Lemma until_free_or_nogrey :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color grey (mk s) 0)) str ->
 state2stream_formula (fun s : state => ~ accessible node (hp s) rt n) str ->
 until
   (state2stream_formula (fun s : state => ~ accessible node (hp s) rt n))
   (free_or_notfree_notacc_nogrey n) str.

unfold state2stream_formula in |- *;
 unfold free_or_notfree_notacc_nogrey in |- *.
simpl in |- *; intros n str H_trace H H_n.
generalize H_trace H_n; clear H_n H_trace.
elim H; clear H str.
intros str H_card H_trace H_n.
elim (eq_dec_color (mk (head_str str) n) free); intro mkhdn.
constructor 1; left; auto.
constructor 1.
right; split; auto.
intros s str H_ev H_ind H_trace H_n.
elim (eq_dec_color (mk s n) free); intro mkhdn.
constructor 1; left; auto.
constructor 2; auto.
inversion H_trace; clear H_trace.
apply H_ind; auto.
clear H2 H0 H s0 str0.
simpl in H1.
inversion H1.
rewrite <- H; simpl in H_n; assumption.
simpl in H_n; apply step_notacces_t with (s := s); auto.
Qed.

End notfree_notacc.

