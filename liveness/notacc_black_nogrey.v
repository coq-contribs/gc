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
(*                          notacc_black_nogrey.v                           *)
(****************************************************************************)

Section notacc_black_nogrey.

Require Export parameters_card.
Require Export lemma_step.
Require Export notfree_notacc.
Require Export mesure.
Require Export Peano_dec.

Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Stream := (stream state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Trace := (trace (fun (a : label) (s t : state) => transition s t a))
  (only parsing).

Definition notacc_black_nogrey_exwhite (s : state) 
  (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\
  mk s n = black /\
  card_color grey (mk s) 0 /\
  (exists w : nat, card_color white (mk s) w /\ w <> 0).

Definition notacc_black_nogrey (s : state) (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\ mk s n = black /\ card_color grey (mk s) 0.

Lemma add_notacc_black_nogrey :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 notacc_black_nogrey_exwhite s n -> add_edge s t -> notacc_black_nogrey t n.

intros s t n H_inv H addedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; split.
info eauto.
split.
info eauto.
inversion_clear H_grey; constructor.
info eauto.
Qed.

Hint Resolve add_notacc_black_nogrey.

Lemma remove_notacc_black_nogrey :
 forall (s t : state) (n : node),
 notacc_black_nogrey_exwhite s n ->
 remove_edge s t -> notacc_black_nogrey t n.

intros s t n H removeedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; split; eauto.
Qed.

Hint Resolve remove_notacc_black_nogrey.

Lemma alloc_notacc_black_nogrey :
 forall (s t : state) (n : node),
 notacc_black_nogrey_exwhite s n -> alloc s t -> notacc_black_nogrey t n.

unfold notacc_black_nogrey_exwhite in |- *; intros s t n H alloc; elim H;
 clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; split.
apply (alloc_notacces_t s t n); auto.
split; auto.
rewrite mksn; discriminate.
split; eauto.
Qed.

Hint Resolve alloc_notacc_black_nogrey.

Lemma gccall_notacc_black_nogrey :
 forall (s t : state) (n : node),
 notacc_black_nogrey_exwhite s n -> gc_call s t -> notacc_black_nogrey t n.

unfold notacc_black_nogrey_exwhite in |- *; intros s t n H gccall; elim H;
 clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; elim gccall; clear gccall.
intros ctls ctlt heap H_col H_init; elim H_white; clear H_white.
intros w H; elim H; clear H.
intros H_white wdifO;
 absurd (exists w : nat, card_color white (mk s) w /\ w = 0).
intro H; elim H; clear H.
intros w' H; elim H; clear H.
intros H_card w'eqO; absurd (w' = 0); auto.
cut (w' = w).
intro w'eqw; rewrite w'eqw; assumption.
apply unicity_card with (M := mk s) (P := fun c : color => c = white);
 assumption.
exists 0; split; auto.
constructor.
intro m; elim (H_col m); intro mksm; rewrite mksm; discriminate.
intros ctls ctlt heap H; elim H; clear H.
inversion H_grey; intros g mksg; absurd (mk s g = grey); auto.
intros ctls ctlt heap H_col m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; split.
rewrite <- heap; assumption.
split.
rewrite <- (mark n); auto.
apply (noteqmar_noteqnod (mk s) n m).
rewrite mksn; rewrite mksm; discriminate.
constructor; intro n'; elim (eq_dec_node n' m).
intro n'eqm; intro mktn'; rewrite <- n'eqm in mktm; absurd (mk t n' = grey);
 auto.
rewrite mktm; discriminate.
intro n'difm; rewrite <- (mark n' n'difm); auto.
Qed.

Hint Resolve gccall_notacc_black_nogrey.

Lemma marknode_notacc_black_nogrey :
 forall (s t : state) (n : node),
 notacc_black_nogrey_exwhite s n -> mark_node s t -> notacc_black_nogrey t n.

unfold notacc_black_nogrey_exwhite in |- *; intros s t n H marknode; elim H;
 clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; elim marknode; clear marknode.
intros ctls ctlt heap H; elim H; clear H.
intros g mksg; absurd (mk s g = grey); inversion H_grey; auto.
Qed.

Hint Resolve marknode_notacc_black_nogrey.

Lemma gcstop_notacc_black_nogrey :
 forall (s t : state) (n : node),
 notacc_black_nogrey_exwhite s n -> gc_stop s t -> notacc_black_nogrey t n.

unfold notacc_black_nogrey_exwhite in |- *; intros s t n H gcstop; elim H;
 clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; split; eauto.
Qed.

Hint Resolve gcstop_notacc_black_nogrey.

Lemma gcfree_notacc_black_nogrey :
 forall (s t : state) (n : node),
 notacc_black_nogrey_exwhite s n -> gc_free s t -> notacc_black_nogrey t n.

unfold notacc_black_nogrey_exwhite in |- *; intros s t n H gcfree; elim H;
 clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; split; eauto.
Qed.

Hint Resolve gcfree_notacc_black_nogrey.

Lemma gcfree1_notacc_black_nogrey :
 forall (s t : state) (n : node),
 sweep_no_greys s ->
 notacc_black_nogrey_exwhite s n -> gc_free1 s t -> notacc_black_nogrey t n.

unfold notacc_black_nogrey_exwhite in |- *; unfold sweep_no_greys in |- *;
 intros s t n H_inv H gcfree; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; split; eauto.
Qed.

Hint Resolve gcfree1_notacc_black_nogrey.

Lemma gcend_notacc_black_nogrey :
 forall (s t : state) (n : node),
 notacc_black_nogrey_exwhite s n -> gc_end s t -> notacc_black_nogrey t n.

unfold notacc_black_nogrey_exwhite in |- *; intros s t n H gcend; elim H;
 clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; split; eauto.
Qed.

Hint Resolve gcend_notacc_black_nogrey.

Lemma step_notacc_black_nogrey :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 sweep_no_greys s ->
 notacc_black_nogrey_exwhite s n ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 notacc_black_nogrey t n.

intros s t n H_inv H_sweep H_n step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve step_notacc_black_nogrey.

Definition notacc_black_nogrey_exwhite_formula (n : node) :
  stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\
     mk s n = black /\
     card_color grey (mk s) 0 /\
     (exists w : nat, card_color white (mk s) w /\ w <> 0)) str.

Definition notacc_black_nogrey_nowhite_formula (n : node) :
  stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\
     mk s n = black /\ card_color grey (mk s) 0 /\ card_color white (mk s) 0)
    str.

Lemma until_no_white :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color white (mk s) 0)) str ->
 always
   (state2stream_formula
      (fun s : state => exists w : nat, card_color white (mk s) w)) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_black_nogrey_exwhite_formula n str ->
 until (fun str => notacc_black_nogrey_exwhite_formula n str)
   (fun str => notacc_black_nogrey_nowhite_formula n str) str.

intros n str H_trace H.
generalize H_trace; elim H; clear H_trace H str.
unfold notacc_black_nogrey_exwhite_formula in |- *;
 unfold state2stream_formula in |- *; simpl in |- *.
intros str H_white H1 H2 H3 H4 H.
clear H1 H2 H3 H4.
elim H; clear H.
intros notacc_n_hd H; elim H; clear H.
intros mkhdn H; elim H; clear H.
intros H_grey H; elim H; clear H.
intros w H; elim H; clear H.
intros H_card wdifO;
 absurd (exists w : nat, card_color white (mk (head_str str)) w /\ w = 0).
intro H; elim H; clear H.
intros w' H; elim H; clear H.
intros H_card' w'difO; absurd (w' = 0); auto.
cut (w' = w).
intro w'eqw; rewrite w'eqw; assumption.
apply
 unicity_card with (M := mk (head_str str)) (P := fun c : color => c = white);
 assumption.
exists 0; split; auto.

(* Induction Step *)

unfold notacc_black_nogrey_exwhite_formula in |- *;
 unfold notacc_black_nogrey_nowhite_formula in |- *.
intros s str H_ev H_ind H_trace H_always_card H_always_sweep H_always_inv H_n.
elim H_n; clear H_n.
simpl in |- *; intros notacc_n_s H; elim H; clear H.
intros mksn H; elim H; clear H.
intros H_grey H_white; inversion H_always_card; clear H0 H s0 str0.
elim H1; clear H1.
simpl in |- *; intros w H_card; elim (eq_nat_dec w 0).
intro weq0; rewrite weq0 in H_card; constructor 1; split; auto.
intro wdif0; constructor 2.
split; auto.
inversion H_trace; inversion H_always_card; inversion H_always_sweep;
 inversion H_always_inv.
clear H13 H12 str3 s3 H9 H8 s2 str2 H5 H4 str1 s1 H0 H s0 str0.
simpl in H1; inversion H1.

(*  s=str0 *)

apply H_ind; try assumption.
unfold state2stream_formula in |- *; simpl in |- *.
rewrite <- H; split; auto.


(* (step s str0) therefore (f n str0) *)

cut (notacc_black_nogrey (head_str str) n).
intro H_def.
elim H_def; clear H_def.
intros acces_n_hd H30; elim H30; clear H30.
intros mknhd H_card_grey.
inversion H2.
rewrite H8 in H4; rewrite H8; clear H5 H8 str0 s0.
elim H4; clear H4.
intros w' H_white'; elim (eq_nat_dec w' 0).
intro w'eq0; rewrite w'eq0 in H_white'; constructor 1; split; auto.
intro w'dif0; apply H_ind; try assumption.
unfold state2stream_formula in |- *; simpl in |- *; split; auto.
split; auto.
split; auto.
exists w'; split; auto.
apply step_notacc_black_nogrey with (s := s); auto.
split; auto.
Qed.


Hint Resolve until_no_white.

Definition notacc_black_nogrey_formula (n : node) : 
  stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\
     mk s n = black /\ card_color grey (mk s) 0) str.


Definition notacc_black_nomeasure_formula (n : node) :
  stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\ mk s n = black /\ mesure (mk s) 0) str.

Lemma equiv_def :
 forall (str : stream state) (n : node),
 notacc_black_nogrey_exwhite_formula n str ->
 notacc_black_nogrey_formula n str.

intros str n H; elim H; clear H.
intros notacc_n_hd H; elim H; clear H.
intros mkhdn H; elim H; clear H.
intros H_grey H_white; split; auto.
Qed.
Hint Resolve equiv_def.

Lemma equiv_def2 :
 forall (str : stream state) (n : node),
 notacc_black_nogrey_nowhite_formula n str ->
 notacc_black_nomeasure_formula n str.

intros str n H; elim H; clear H.
intros notacc_n_hd H; elim H; clear H.
intros mkhdn H; elim H; clear H.
intros H_grey H_white; split; auto.
split; auto.
replace 0 with (0 + 0); auto with arith.
constructor; assumption.
Qed.
Hint Resolve equiv_def2.

Lemma until_no_measure :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color white (mk s) 0)) str ->
 always
   (state2stream_formula
      (fun s : state => exists w : nat, card_color white (mk s) w)) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_black_nogrey_formula n str ->
 until (fun str => notacc_black_nogrey_formula n str)
   (fun str => notacc_black_nomeasure_formula n str) str.

intros n str H_trace H_ev H_always_white H_always_sweep H_always_inv H_n;
 elim H_n; clear H_n.
intros notacc_n_hd H; elim H; clear H.
intros mkhdn H_card.
inversion H_always_white.
rewrite H1 in H; rewrite H1; clear H0 H1 str0 s0.
elim H; clear H.
intros w H_white; elim (eq_nat_dec w 0).
intro weq0; rewrite weq0 in H_white; constructor 1; split; auto.
split; auto.
replace 0 with (0 + 0); auto with arith.
constructor; assumption.
intro wdif0.
apply
 until_implies_until_stream
  with
    (P := fun str => notacc_black_nogrey_exwhite_formula n str)
    (Q := fun str => notacc_black_nogrey_nowhite_formula n str); 
 eauto.
apply until_no_white; auto.
split; auto.
split; auto.
split; auto.
exists w; auto.
Qed.

End notacc_black_nogrey.