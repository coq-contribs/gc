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
(*                             notacc_init.v                                *)
(****************************************************************************)

Section notacc_init.

Require Export parameters_card.
Require Export lemma_step.
Require Export notfree_notacc.
Require Export mesure.

Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Stream := (stream state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Trace := (trace (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Fair_step :=
  (fair_step (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).
Notation Strong_fairstr :=
  (strong_fairstr (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).
Notation Fairstr :=
  (fairstr (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).

Lemma fairstep_implies_initcol :
 forall s t : state,
 mesure (mk s) 0 ->
 fair_step (fun (a : label) (s t : state) => transition s t a) fair s t ->
 init_color (mk s) (mk t).

intros s t H_mes H; inversion_clear H.
generalize (refl_equal a); pattern a at -1 in |- *; case a; intro H_label.

(* add, remove, alloc *)
absurd (fair a); [ rewrite H_label; auto | auto ].
absurd (fair a); [ rewrite H_label; auto | auto ].
absurd (fair a); [ rewrite H_label; auto | auto ].

(*gc_call*)

rewrite H_label in H1; inversion_clear H1.
elim H; clear H; auto.
intros ctls ctlt heap H; elim H; clear H.
inversion H_mes; intros g' mksg'; absurd (card_color grey (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s g' = grey); auto.
cut (g = 0);
 [ intro geq0; rewrite <- geq0; assumption
 | rewrite (plus_comm g w) in H; apply (plus_O_O w g); assumption ].
intros ctls ctlt heap H_col m mksm; inversion H_mes;
 absurd (card_color white (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s m = white); auto.
cut (w = 0);
 [ intro weq0; rewrite <- weq0; assumption
 | apply (plus_O_O g w); assumption ].

(* mark*)

rewrite H_label in H1; inversion_clear H1.
elim H; clear H; auto.
intros ctls ctlt heap H; elim H; clear H.
inversion H_mes; intros g' mksg'; absurd (card_color grey (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s g' = grey); auto.
cut (g = 0);
 [ intro geq0; rewrite <- geq0; assumption
 | rewrite (plus_comm g w) in H; apply (plus_O_O w g); assumption ].

(* gc_stop *)
absurd (fair a); [ rewrite H_label; auto | auto ].

(* gc_free *)

rewrite H_label in H1; inversion_clear H1.
elim H; clear H; auto.
intros ctls ctlt heap H_col m mksm; inversion H_mes;
 absurd (card_color white (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s m = white); auto.
cut (w = 0);
 [ intro weq0; rewrite <- weq0; assumption
 | apply (plus_O_O g w); assumption ].

(*gc_free1 *)

rewrite H_label in H1; inversion_clear H1.
elim H; clear H; auto.
intros ctls ctlt heap m mksm; inversion H_mes;
 absurd (card_color white (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s m = white); auto.
cut (w = 0);
 [ intro weq0; rewrite <- weq0; assumption
 | apply (plus_O_O g w); assumption ].

(*gc_end*)
absurd (fair a); [ rewrite H_label; auto | auto ].
Qed.

Hint Resolve fairstep_implies_initcol.

Lemma fairstep_implies_gc_call :
 forall s t : state,
 mesure (mk s) 0 ->
 fair_step (fun (a : label) (s t : state) => transition s t a) fair s t ->
 gc_call s t.

intros s t H_mes H; inversion_clear H.
generalize (refl_equal a); pattern a at -1 in |- *; case a; intro H_label.

(* add, remove, alloc *)
absurd (fair a); [ rewrite H_label; auto | auto ].
absurd (fair a); [ rewrite H_label; auto | auto ].
absurd (fair a); [ rewrite H_label; auto | auto ].
rewrite H_label in H1.
inversion H1; auto.
rewrite H_label in H1; inversion_clear H1.
elim H; clear H; auto.
intros ctls ctlt heap H; elim H; clear H.
inversion H_mes; intros g' mksg'; absurd (card_color grey (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s g' = grey); auto.
cut (g = 0);
 [ intro geq0; rewrite <- geq0; assumption
 | rewrite (plus_comm g w) in H; apply (plus_O_O w g); assumption ].

(* gc_stop *)
absurd (fair a); [ rewrite H_label; auto | auto ].

(* gc_free *)

rewrite H_label in H1; inversion_clear H1.
elim H; clear H; auto.
intros ctls ctlt heap H_col m mksm; inversion H_mes;
 absurd (card_color white (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s m = white); auto.
cut (w = 0);
 [ intro weq0; rewrite <- weq0; assumption
 | apply (plus_O_O g w); assumption ].

(*gc_free1 *)

rewrite H_label in H1; inversion_clear H1.
elim H; clear H; auto.
intros ctls ctlt heap m mksm; inversion H_mes;
 absurd (card_color white (mk s) 0).
intro H'; inversion_clear H'; absurd (mk s m = white); auto.
cut (w = 0);
 [ intro weq0; rewrite <- weq0; assumption
 | apply (plus_O_O g w); assumption ].

(*gc_end*)
absurd (fair a); [ rewrite H_label; auto | auto ].
Qed.

Lemma init_implies_whiteorfree :
 forall s t : state,
 mesure (mk s) 0 ->
 init_color (mk s) (mk t) ->
 forall n : node, n <> rt -> mk t n = white \/ mk t n = free.

intros s t H_mes init n ndifrt; elim init; clear init.
intros mktrt H; elim H; clear H.
intros mark1 mark2; elim (eq_dec_color (mk s n) black); intro mksn.
left; apply mark1; assumption.
cut (mk s n = black \/ mk s n = free).
intro H; elim H; clear H; intro mksn2.
absurd (mk s n = black); assumption.
right; rewrite (mark2 n ndifrt mksn); assumption.
inversion H_mes.
cut (g = 0).
intro geq0; cut (w = 0).
intro weq0; rewrite geq0 in H0; rewrite weq0 in H1; inversion_clear H0;
 inversion_clear H1.
generalize (refl_equal (mk s n)); pattern (mk s n) at -1 in |- *;
 case (mk s n); intro mksn2.
absurd (mk s n = white); auto.
left; reflexivity.
absurd (mk s n = grey); auto.
right; reflexivity.
apply (plus_O_O g w); assumption.
rewrite (plus_comm g w) in H; apply (plus_O_O w g); assumption.
Qed.

Definition notacc_black_nomeasure (s : state) (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\ mk s n = black /\ mesure (mk s) 0.

Definition notacc_white_init (s : state) (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\
  mk s n = white /\
  mk s rt = grey /\
  (forall n : node, n <> rt -> mk s n = white \/ mk s n = free).

Lemma add_idem_or_init :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 notacc_black_nomeasure s n ->
 add_edge s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H_inv H addedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes; left; split.
eapply add_notaccess_notaccest.
eexact notacc_n_s.
eexact addedge.

split.
eapply add_blacks_blackt.
eexact addedge.
    
eexact mksn.
    
eapply add_mesure.
eexact H_mes.
    
eexact addedge.
Qed.

Hint Resolve add_idem_or_init.

Lemma remove_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 remove_edge s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H removeedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes; left; split; eauto.
Qed.

Hint Resolve remove_idem_or_init.

Lemma alloc_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 alloc s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H alloc; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes.
left; split.
apply (alloc_notacces_t s t n); auto.
split; [ rewrite mksn; discriminate | assumption ].
apply conj.
    eapply alloc_blacks_blackt.
    eexact mksn.
    
    eexact alloc.
    
    eapply alloc_mesure.
    eexact H_mes.
    
    eexact alloc.

Qed.

Hint Resolve alloc_idem_or_init.

Lemma gccall_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 gc_call s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H gccall; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes; elim gccall; clear gccall.
intros ctls ctlt heap H_col H_init; elim H_init; clear H_init.
intros mktrt H; elim H; clear H.
intros mark1 mark2; right; split.
rewrite heap; assumption.
split.
elim (eq_dec_node n rt).
intro neqrt; absurd (accessible node (hp s) rt n);
 [ auto | rewrite neqrt; constructor ].
intro ndifrt; apply mark1; assumption.
split; auto.
intros m mdifrt; elim (eq_dec_color (mk s m) black); intro mksm.
left; apply mark1; assumption.
right; rewrite (mark2 m); auto.
elim (H_col m); intro mksm2; auto.
absurd (mk s m = black); auto.
intros ctls ctlt heap H'; inversion H_mes; elim H'; clear H'.
intros g0 mksg0; absurd (mk s g0 = grey); auto.
cut (g = 0);
 [ intro geq0; rewrite geq0 in H0; inversion_clear H0; auto
 | rewrite (plus_comm g w) in H; apply (plus_O_O w g); assumption ].
intros ctls ctlt heap H_col m mksm; inversion H_mes; absurd (mk s m = white);
 auto.
cut (w = 0);
 [ intro weq0; rewrite weq0 in H1; inversion_clear H1; auto
 | apply (plus_O_O g w); assumption ].
Qed.

Hint Resolve gccall_idem_or_init.

Lemma marknode_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 mark_node s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H marknode; elim H; clear H.
intros notacc_n_s H; elim H; clear H.  
intros mksn H_mes; inversion H_mes; elim marknode; clear marknode.
intros ctls ctlt heap H'; elim H'; clear H'.
intros g0 mksg0; absurd (mk s g0 = grey); auto.
cut (g = 0);
 [ intro geq0; rewrite geq0 in H0; inversion_clear H0; auto
 | rewrite (plus_comm g w) in H; apply (plus_O_O w g); assumption ].
Qed.

Hint Resolve marknode_idem_or_init.

Lemma gcstop_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 gc_stop s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H gcstop; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes; left; split.
eapply gcstop_notaccess_notaccest.
eexact notacc_n_s.
    
eexact gcstop.
 
split.
eapply gcstop_blacks_blackt.
    eexact gcstop.
    
    eexact mksn.
    
    eapply gcstop_mesure.
    eexact H_mes.
    
    eexact gcstop.

Qed.

Hint Resolve gcstop_idem_or_init.

Lemma gcfree_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 gc_free s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H gcfree; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes; left; split.
eapply gcfree_notaccess_notaccest.
    eexact notacc_n_s.
    
    eexact gcfree.

split.
eapply gcfree_blacks_blackt.
    eexact gcfree.
    
    eexact mksn.

inversion H_mes; constructor.

eapply gcfree_grey.
    eexact H0.
    
    eexact gcfree.

cut (w = 0);
 [ intro weq0; rewrite weq0; rewrite weq0 in H1; inversion H1; constructor;
    eauto
 | apply (plus_O_O g w); assumption ].
Qed.

Hint Resolve gcfree_idem_or_init.

Lemma gcfree1_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 gc_free1 s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H gcfree1; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes; left; split.

 eapply gcfree1_notaccess_notaccest.
    eexact notacc_n_s.
    
    eexact gcfree1.

split.

eapply gcfree1_blacks_blackt.
    eexact gcfree1.
    
    eexact mksn.

inversion H_mes; constructor.

 eapply gcfree1_grey.
    eexact H0.
    
    eexact gcfree1.

cut (w = 0);
 [ intro weq0; rewrite weq0; rewrite weq0 in H1; inversion H1; constructor;
    eauto
 | apply (plus_O_O g w); assumption ].
Qed.

Hint Resolve gcfree1_idem_or_init.

Lemma gcend_idem_or_init :
 forall (s t : state) (n : node),
 notacc_black_nomeasure s n ->
 gc_end s t -> notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H gcend; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_mes; left; split; eauto.
Qed.

Hint Resolve gcend_idem_or_init.

Lemma step_idem_or_init :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 notacc_black_nomeasure s n ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 notacc_black_nomeasure t n \/ notacc_white_init t n.

intros s t n H_inv H_n step; elim step; intro a; case a; intro trans;
 inversion_clear trans; eauto.
Qed.

Hint Resolve step_idem_or_init.

Definition notacc_black_nomeasure_formula (n : node) :
  stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\ mk s n = black /\ mesure (mk s) 0) str.

Definition notacc_white_init_formula (n : node) : stream_formula state :=
  fun str =>
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\
     mk s n = white /\
     mk s rt = grey /\
     (forall n : node, n <> rt -> mk s n = white \/ mk s n = free)) str.

Lemma null_measure_grey_white :
 forall s : state,
 mesure (mk s) 0 -> card_color grey (mk s) 0 /\ card_color white (mk s) 0.
intros s H; inversion H; clear H.
rewrite H0.
cut (g = 0).
cut (w = 0).
intros H_w H_g.
split.
rewrite <- H_g; assumption.
rewrite <- H_w; assumption.
cut (g = 0 /\ w = 0).
intro H; elim H; auto.
apply plus_is_O; auto.
cut (g = 0 /\ w = 0).
intro H; elim H; auto.
apply plus_is_O; auto.
Qed.

Lemma step_initcolor :
 forall (n : node) (s t : state),
 notacc_black_nomeasure s n ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 init_color (mk s) (mk t) -> notacc_white_init t n.


intros n s t H_n H_step H_initcolor.
elim H_n; clear H_n.
intros notacc H; elim H; clear H.
intros H_black H_mes0.
elim H_initcolor; clear H_initcolor.
intros H_rtgrey H; elim H; clear H.
intros H1 H2.
split.
apply step_notacces_t with (s := s); auto.
split; try assumption.
rewrite H_black; discriminate.
split; auto.
apply H1; auto.
intro H_eq.
absurd (accessible node (hp s) rt n); auto.
rewrite H_eq; constructor.
split; auto.


clear H_step notacc H_black H_rtgrey n.
intros n H_noteq.
elim (eq_dec_color (mk s n) black).
left; auto.
clear H1.
right.
cut (card_color grey (mk s) 0 /\ card_color white (mk s) 0); auto.
intro H; elim H; clear H. 
clear H_mes0; intros Hg Hw.
inversion_clear Hg; inversion_clear Hw.

rewrite (H2 n H_noteq b).
clear H2 H_noteq.
cut (forall x : color, x = mk s n -> x = free); auto.
intro x; case x; clear x.

intro Hw; absurd (white = mk s n); auto.
intro Hb; absurd (black = mk s n); auto.
intro Hg; absurd (grey = mk s n); auto.
intro; reflexivity.
apply null_measure_grey_white; assumption.
Qed.


Lemma until_no_measure_init :
 forall (n : node) (str : stream state),
 strong_fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_black_nomeasure_formula n str ->
 until (fun str => notacc_black_nomeasure_formula n str)
   (fun str => notacc_white_init_formula n str) str.

intros n str H_fair; inversion H_fair.
rewrite H1 in H; rewrite H1; clear H0 H1 s0 str0 H_fair.
elim H; clear H str.


(* Base case *)


intro str; case str; clear str. 
unfold notacc_black_nomeasure_formula in |- *;
 unfold state2stream_formula in |- *; simpl in |- *.
intros s str H_fairstep H_trace H_always_inv H_n.
constructor 2; auto.
constructor 1.
elim H_n.
intros A B; elim B; clear B.
intros B M.
cut (init_color (mk s) (mk (head_str str))).
2: apply fairstep_implies_initcol; auto.
intro init_col.
unfold notacc_white_init_formula in |- *; unfold state2stream_formula in |- *.
replace
 (~ accessible node (hp (head_str str)) rt n /\
  mk (head_str str) n = white /\
  mk (head_str str) rt = grey /\
  (forall n0 : node,
   n0 <> rt -> mk (head_str str) n0 = white \/ mk (head_str str) n0 = free))
 with (notacc_white_init (head_str str) n); auto.
apply step_initcolor with (s := s).
unfold notacc_black_nomeasure in |- *; auto.
inversion_clear H_fairstep.
apply C_trans with (a := a); assumption.
apply fairstep_implies_initcol with (s := s); assumption.

(*induction step*)

intros s str H_eventually H_ind H_trace H_always_inv H_n.
inversion H_trace; inversion H_always_inv.
clear H4 H3 str1 s1 H0 H s0 str0.
constructor 2; try assumption.
simpl in H1; inversion H1.
apply H_ind; try assumption.
rewrite H in H_n; auto.
cut
 (notacc_black_nomeasure (head_str str) n \/
  notacc_white_init (head_str str) n).
intro H'; elim H'; clear H'.
intro H_n'; apply H_ind; auto.
intro H_n'; constructor 1; auto.
apply step_idem_or_init with (s := s); auto.
Qed.


End notacc_init.