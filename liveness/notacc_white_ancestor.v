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
(*                         notacc_white_ancestor.v                          *)
(****************************************************************************)

Section notacc_white_ancestor.

Require Export reachable.
Require Export lemma_step.
Require Export notfree_notacc.
Require Export notacc_white_nogrey.
Require Export Peano_dec.


Notation Reachable := (reachable node) (only parsing).
Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Stream := (stream state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Trace := (trace (fun (a : label) (s t : state) => transition s t a))
  (only parsing).

Definition notacc_white_exgrey_reach (s : state) (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\
  mk s n = white /\
  (exists g : nat, card_color grey (mk s) g /\ g <> 0) /\
  (forall m : node,
   reachable node (hp s) m n -> mk s m = white \/ mk s m = free).

Definition notacc_white_reach (s : state) (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\
  mk s n = white /\
  (forall m : node,
   reachable node (hp s) m n -> mk s m = white \/ mk s m = free).

Lemma add_notacc_white_reach :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 notacc_white_exgrey_reach s n -> add_edge s t -> notacc_white_reach t n.

intros s t n H_inv H addedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; split.
eapply add_notaccess_notaccest.
eexact notacc_n_s.
eexact addedge.
split.
 eapply add_white_nogrey.
 eexact mksn.
eexact notacc_n_s.
 eexact addedge.
intro m; intro H; eapply add_ancestor_col.
eexact notacc_n_s.
eexact H_anc.
eexact addedge.
eexact H.

Qed.

Hint Resolve add_notacc_white_reach.

Lemma remove_notacc_white_reach :
 forall (s t : state) (n : node),
 notacc_white_exgrey_reach s n -> remove_edge s t -> notacc_white_reach t n.

intros s t n H removeedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; split; eauto.
Qed.

Hint Resolve remove_notacc_white_reach.

Lemma alloc_notacc_white_reach :
 forall (s t : state) (n : node),
 notacc_white_exgrey_reach s n -> alloc s t -> notacc_white_reach t n.

intros s t n H alloc; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; split.
apply alloc_notacces_t with (s := s); try assumption.
split; [ rewrite mksn; discriminate | assumption ].
split.
apply alloc_whites_whitet with (s := s); assumption.
intros m H_reach; apply alloc_ancestor_col with (s := s) (n := n);
 try assumption.
apply alloc_notacces_t with (s := s); try assumption.
split; [ rewrite mksn; discriminate | assumption ].
Qed.

Hint Resolve alloc_notacc_white_reach.

Lemma gccall_notacc_white_reach :
 forall (s t : state) (n : node),
 notacc_white_exgrey_reach s n -> gc_call s t -> notacc_white_reach t n.

intros s t n H gccall; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; elim gccall; clear gccall.

(* 1st case impossible no grey *)
intros ctls ctlt heap H_col H_init; elim H_grey; clear H_grey.
intros g H; elim H; clear H.
intros H_grey gdifO.
absurd (exists g : nat, card_color grey (mk s) g /\ g = 0).
intro H; elim H; clear H.
intros g' H; elim H; clear H.
intros H_grey' g'eqO; absurd (g' = 0); auto.
cut (g' = g);
 [ intro g'eqg; rewrite g'eqg; assumption
 | apply unicity_card with (M := mk s) (P := fun c : color => c = grey);
    assumption ].
exists 0; split; auto.
constructor.
intro m; elim (H_col m); intro mksm; rewrite mksm; discriminate.


(* 2nd case : a grey is blackened  *)
intros ctls ctlt heap grey_node; split.
rewrite heap; assumption.
split;
 [ apply grey_white with (s := s); auto
 | intros m H_reach_m; apply grey_ancestor_col with (s := s) (n := n); auto ].

(* grey_white : a white node remains white 
   grey_ancestor_col: an ancestor which is white or free does not change *)

(* 3rd case g cannot be 0 *)
intros ctls ctlt heap H_col m mksm upd_col; elim H_grey; clear H_grey.
intros g H; elim H; clear H.
intros H_grey gdifO;
 absurd (exists g : nat, card_color grey (mk s) g /\ g = 0).
intro H; elim H; clear H.
intros g' H; elim H; clear H.
intros H_grey' g'eqO; absurd (g' = 0); auto.
cut (g' = g);
 [ intro g'eqg; rewrite g'eqg; assumption
 | apply unicity_card with (M := mk s) (P := fun c : color => c = grey);
    assumption ].
exists 0; split; [ constructor; auto | auto ].
Qed.

Hint Resolve gccall_notacc_white_reach.

Lemma mark_notacc_white_reach :
 forall (s t : state) (n : node),
 notacc_white_exgrey_reach s n -> mark_node s t -> notacc_white_reach t n.

intros s t n H marknode; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; split; eauto.
Qed.

Hint Resolve mark_notacc_white_reach.

Lemma gcstop_notacc_white_reach :
 forall (s t : state) (n : node),
 notacc_white_exgrey_reach s n -> gc_stop s t -> notacc_white_reach t n.

intros s t n H gcstop; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; split; eauto.
Qed.

Hint Resolve gcstop_notacc_white_reach.

Lemma gcfree_notacc_white_reach :
 forall (s t : state) (n : node),
 notacc_white_exgrey_reach s n -> gc_free s t -> notacc_white_reach t n.

intros s t n H gcfree; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; elim gcfree; clear gcfree.
intros ctls ctlt H_col; elim H_grey; clear H_grey.
intros g H; elim H; clear H.
intros H_grey gdifO;
 absurd (exists g : nat, card_color grey (mk s) g /\ g = 0).
intro H; elim H; clear H.
intros g' H; elim H; clear H.
intros H_grey' g'eqO; absurd (g' = 0); auto.
cut (g' = g);
 [ intro g'eqg; rewrite g'eqg; assumption
 | apply unicity_card with (M := mk s) (P := fun c : color => c = grey);
    assumption ].
exists 0; split; [ constructor; auto | auto ].
Qed.

Hint Resolve gcfree_notacc_white_reach.

Lemma gcfree1_notacc_white_reach :
 forall (s t : state) (n : node),
 sweep_no_greys s ->
 notacc_white_exgrey_reach s n -> gc_free1 s t -> notacc_white_reach t n.

unfold sweep_no_greys in |- *; intros s t n H_sweep H gcfree1; elim H;
 clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; elim gcfree1; clear gcfree1.
intros ctls ctlt; elim H_grey; clear H_grey.
intros g H; elim H; clear H.
intros H_grey gdifO;
 absurd (exists g : nat, card_color grey (mk s) g /\ g = 0).
intro H; elim H; clear H.
intros g' H; elim H; clear H.
intros H_grey' g'eqO; absurd (g' = 0); auto.
cut (g' = g);
 [ intro g'eqg; rewrite g'eqg; assumption
 | apply unicity_card with (M := mk s) (P := fun c : color => c = grey);
    assumption ].
exists 0; split; [ constructor; auto | auto ].
Qed.

Hint Resolve gcfree1_notacc_white_reach.

Lemma gcend_notacc_white_reach :
 forall (s t : state) (n : node),
 notacc_white_exgrey_reach s n -> gc_end s t -> notacc_white_reach t n.

intros s t n H gcend; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_anc; split; eauto.
Qed.

Hint Resolve gcend_notacc_white_reach.

Lemma step_notacc_white_reach :
 forall (s t : state) (n : node),
 sweep_no_greys s ->
 nogrey_accn_imp_blackn s ->
 notacc_white_exgrey_reach s n ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 notacc_white_reach t n.

intros s t n H_sweep H_inv H_n step; elim step; intro a; case a; intro trans;
 inversion_clear trans; eauto.
Qed.

Hint Resolve step_notacc_white_reach.

Definition notacc_white_exgrey_reach_formula (n : node) :
  stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\
     mk s n = white /\
     (exists g : nat, card_color grey (mk s) g /\ g <> 0) /\
     (forall m : node,
      reachable node (hp s) m n -> mk s m = white \/ mk s m = free)) str.

Definition notacc_white_reach_formula (n : node) : 
  stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\
     mk s n = white /\
     (forall m : node,
      reachable node (hp s) m n -> mk s m = white \/ mk s m = free) /\
     card_color grey (mk s) 0) str.

Lemma until_no_grey :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color grey (mk s) 0)) str ->
 always
   (state2stream_formula
      (fun s : state => exists w : nat, card_color grey (mk s) w)) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_white_exgrey_reach_formula n str ->
 until (fun str => notacc_white_exgrey_reach_formula n str)
   (fun str => notacc_white_reach_formula n str) str.

intros n str H_trace H; generalize H_trace.
elim H; clear H H_trace str.
intros str H_card H_trace H_always_grey H_always_sweep H_always_inv H_n.
elim H_n; clear H_n.

(* base case *)
intros notacc_n H; elim H; clear H.
intros mkhdn H; elim H; clear H.
intros H_grey H_white.
constructor 1; split; auto.

(* induction step *)
intros s str H_eventually H_ind H_trace H_always_grey H_always_sweep
 H_always_inv H_n.
elim H_n; clear H_n.
intros notacc_n H; elim H; clear H.
intros mkhdn H; elim H; clear H.
intros H_grey H_white.
inversion H_always_grey; clear H0 H s0 str0.
elim H1; clear H1; simpl in |- *; intros g H_card.
constructor 2.
split; auto.

(* 2nd goal of constructor 2 *)

inversion H_trace; inversion H_always_grey; inversion H_always_sweep;
 inversion H_always_inv.
clear H13 H12 str3 s3 H9 H8 s2 str2 H5 H4 str1 s1 H0 H s0 str0.
simpl in H1; inversion H1.
apply H_ind; try assumption.
unfold notacc_white_exgrey_reach_formula in |- *;
 unfold state2stream_formula in |- *.
rewrite <- H; split; auto.
cut (notacc_white_reach (head_str str) n).
intro H_def; elim H_def; clear H_def.
intros notacc_hd_n H'; elim H'; clear H'.
intros mhdn H_reach.
inversion H2.
rewrite H8 in H4; rewrite H8; clear H5 H8 str0 s0.
elim H4; clear H4.
intros g' H_grey'.
elim (eq_nat_dec g' 0).
intro g'eq0; rewrite g'eq0 in H_grey'; constructor 1; split; auto.
intro g'dif0; apply H_ind; try assumption.
unfold notacc_white_exgrey_reach_formula in |- *;
 unfold state2stream_formula in |- *; simpl in |- *; 
 split; auto.
split; auto.
split; auto.
exists g'; split; auto.
apply step_notacc_white_reach with (s := s); auto.
split; auto.
Qed.



Hint Resolve until_no_grey.

Lemma equivalent_def :
 forall (n : node) (str : stream state),
 notacc_white_reach_formula n str -> notacc_white_nogrey_formula n str.

intros n str H; elim H; clear H.
intros notacc_n H; elim H; clear H.
intros mkhdn H; elim H; clear H.
intros H_reach H_grey; split; auto.
Qed.

Hint Resolve equivalent_def.

Lemma until_no_grey_without_reach :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color grey (mk s) 0)) str ->
 always
   (state2stream_formula
      (fun s : state => exists w : nat, card_color grey (mk s) w)) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_white_exgrey_reach_formula n str ->
 until (fun str => notacc_white_exgrey_reach_formula n str)
   (fun str => notacc_white_nogrey_formula n str) str.

intros n str H_trace H_always_ev H_always_card H_always_sweep H_always_inv
 H_n.
apply
 until_implies_until_stream
  with
    (P := fun str => notacc_white_exgrey_reach_formula n str)
    (Q := fun str => notacc_white_reach_formula n str); 
 eauto.
Qed.

Hint Resolve until_no_grey_without_reach.

Lemma notacc_white_nogrey_eventually_free :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color grey (mk s) 0)) str ->
 always
   (Eventually
      (state2stream_formula (fun s : state => card_color white (mk s) 0)))
   str ->
 always
   (state2stream_formula
      (fun s : state => exists w : nat, card_color grey (mk s) w)) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_white_exgrey_reach_formula n str ->
 Eventually (state2stream_formula (fun s : state => mk s n = free)) str.

intros n str H_trace H_grey H_always_white H_always_ex_grey H_always_sweep
 H_always_inv H_n.
cut
 (until (fun str => notacc_white_exgrey_reach_formula n str)
    (fun str => notacc_white_nogrey_formula n str) str); 
 eauto.
intro H_until; generalize H_trace H_always_sweep H_always_inv H_always_white.
clear H_always_inv H_always_sweep H_always_ex_grey H_always_white H_grey
 H_trace H_n.
elim H_until; clear H_until.
clear str.
intros str H_n H_trace H_sweep H_nogrey H_white.
inversion H_white.
rewrite H1.
apply white_notacc_nogrey_until_eventually_free; auto.
rewrite <- H1; assumption.

(* Induction Step*)
clear str.
intros s str H_n H_until H_ind H_trace H_always_sweep H_always_inv
 H_always_white.
inversion H_trace; inversion H_always_sweep; inversion H_always_inv;
 inversion H_always_white.
constructor 2; apply H_ind; auto.
Qed.

End notacc_white_ancestor.

Hint Resolve notacc_white_nogrey_eventually_free.



