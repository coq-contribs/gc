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
(*                               fairstr.v                                  *)
(****************************************************************************)

Section fairstr.

Require Export mesure.
Require Export safety.
Require Export gc.
Require Export card.
Require Export unicite_mes.
Require Import Bool.
Require Import Sumbool.

Notation Stream := (stream state) (only parsing).
Notation Fairstr :=
  (fairstr (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).
Notation Fair_step :=
  (fair_step (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).
Notation Run :=
  (run init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Safe :=
  (safe init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).

Definition update_color_marknode (m : marking) (h : heap) 
  (c0 c1 c2 : color) (g n : node) :=
  match eq_dec_node n g with
  | left _ => c0
  | right _ =>
      match sumbool_of_bool (h g n) with
      | left _ =>
          match eq_dec_color (m n) c1 with
          | left _ => c2
          | right _ => m n
          end
      | right _ => m n
      end
  end.

Lemma exist_grey_node :
 forall (g : node) (m : marking) (h : heap),
 m g = grey ->
 exists m' : marking,
   m' g = black /\
   (forall n : node, h g n = true /\ m n = white -> m' n = grey) /\
   (forall n : node, n <> g /\ h g n = true /\ m n <> white -> m' n = m n) /\
   (forall n : node, n <> g /\ h g n = false -> m' n = m n).

intros g m h mg; split with (update_color_marknode m h black white grey g).
unfold update_color_marknode in |- *; split.
case (eq_dec_node g g); auto.
intro gdifg; absurd (g = g); auto.
split.
intros n H_n; elim H_n; clear H_n.
intros hgn mn; case (eq_dec_node n g).
intro neqg; absurd (n = g); auto.
apply (noteqmar_noteqnod m n g); auto.
rewrite mn; rewrite mg; discriminate.
intro ndifg; case (sumbool_of_bool (h g n)); intro hgn2.
case (eq_dec_color (m n) white); intro mn2; auto.
absurd (m n = white); assumption.
absurd (h g n = false); auto.
intro hgn3; apply (eq_true_false_abs (h g n)); assumption.
split.
intros n H_n; elim H_n; clear H_n.
intros ndifg H; elim H; clear H.
intros hgn mn; case (eq_dec_node n g).
intro neqg; absurd (n = g); auto.
intro ndifg2; case (sumbool_of_bool (h g n)); intro hgn2; auto.
case (eq_dec_color (m n) white); intro mn2; auto.
absurd (m n = white); auto.
intros n H; elim H; clear H.
intros ndifg hgn; case (eq_dec_node n g).
intro neqg; absurd (n = g); auto.
intro ndifg2; case (sumbool_of_bool (h g n)); intro hgn2; auto.
absurd (h g n = true); auto.
intro hgn3; apply (eq_true_false_abs (h g n)); auto.
Qed.

Hint Resolve exist_grey_node.

Lemma call_exist_grey_fair :
 forall s : state,
 ctl s = mutate ->
 (exists n : node, mk s n = grey) ->
 exists t : state,
   fair_step (fun (a : label) (s t : state) => transition s t a) fair s t.

intros s ctls H; elim H; clear H.
intros g mksg; elim (exist_grey_node g (mk s) (hp s)); try assumption.
intros m' H; elim H; clear H.
intros m'g H; elim H; clear H.
intros H_col1 H; elim H; clear H.
intros H_col2 H_col3; exists (c_state (hp s) m' mark);
 apply c_fstep with (a := label_call); unfold fair in |- *; 
 auto.
constructor; apply call_exist_grey; auto.
apply grey_node with (g := g); auto.
intros n H; elim H; clear H.
intros ndifg H; elim H; clear H.
intro H; elim H; clear H.
intros hsgn mksn; symmetry  in |- *; apply H_col2; auto.
intro hsgn; symmetry  in |- *; apply H_col3; auto.
Qed.

Hint Resolve call_exist_grey_fair.

Definition update_init_color (m : marking) (c0 c1 c2 : color) 
  (n : node) :=
  match eq_dec_node n rt with
  | left _ => c0
  | right _ =>
      match eq_dec_color (m n) c1 with
      | left _ => c2
      | right _ => m n
      end
  end.

Lemma exist_update_init_color :
 forall m : marking, exists m' : marking, init_color m m'.

intro m; unfold init_color in |- *.
split with (update_init_color m grey black white);
 unfold update_init_color in |- *; split.
case (eq_dec_node rt rt); auto.
intro rtdifrt; absurd (rt = rt); auto.
split.
intros n ndifrt mn; case (eq_dec_node n rt).
intro neqrt; absurd (n = rt); auto.
intro H; clear H; case (eq_dec_color (m n) black); auto.
intro mn2; absurd (m n = black); auto.
intros n ndifrt mn; case (eq_dec_node n rt).
intro neqrt; absurd (n = rt); auto.
intro H; clear H; case (eq_dec_color (m n) black); auto.
intro mn2; absurd (m n = black); auto.
Qed.

Hint Resolve exist_update_init_color.

Lemma call_gc_fair :
 forall s : state,
 ctl s = mutate ->
 (forall n : node, mk s n <> white) ->
 (forall n : node, mk s n <> grey) ->
 exists t : state,
   fair_step (fun (a : label) (s t : state) => transition s t a) fair s t. 

intros s ctls H_white H_grey.
cut (exists m' : marking, init_color (mk s) m'); eauto.
intro H_mkt; elim H_mkt; clear H_mkt.
intros mk' init_mk'; exists (c_state (hp s) mk' mark);
 apply c_fstep with (a := label_call); unfold fair in |- *; 
 auto.
constructor; apply call_gc; auto.
intro n; generalize (refl_equal (mk s n)); pattern (mk s n) at -1 in |- *;
 case (mk s n); intro mksn.
absurd (mk s n = white); auto. 
left; auto.
absurd (mk s n = grey); auto.
right; auto.
Qed.

Hint Resolve call_gc_fair.

Lemma exist_update_color :
 forall (m : marking) (n : node) (c : color),
 m n = white -> exists m' : marking, update_color m m' c n.

intros m n c mn; unfold update_color in |- *.
elim (exist_updated node color c m n); intros m' H_m'; exists m'; assumption.
Qed.

Hint Resolve exist_update_color.

Lemma no_grey_but_white_fair :
 forall s : state,
 ctl s = mutate ->
 (forall n : node, mk s n <> grey) ->
 (exists n : node, mk s n = white) ->
 exists t : state,
   fair_step (fun (a : label) (s t : state) => transition s t a) fair s t. 

intros s ctls H_col H_white; elim H_white; clear H_white.
intros n mksn; cut (exists m' : marking, update_color (mk s) m' free n);
 eauto.
intro H_m'; elim H_m'; clear H_m'.
intros mk' upd_col.
exists (c_state (hp s) mk' mark).
apply c_fstep with (a := label_call).
unfold fair in |- *; auto.
constructor; apply init_no_greys_but_white with (m := n); auto.
Qed.

Hint Resolve no_grey_but_white_fair.

Lemma marknode_fair :
 forall s : state,
 ctl s = mark ->
 (exists n : node, mk s n = grey) ->
 exists t : state,
   fair_step (fun (a : label) (s t : state) => transition s t a) fair s t.

intros s ctls H; elim H; clear H.
intros g mksg; elim (exist_grey_node g (mk s) (hp s)); try assumption.
intros m' H; elim H; clear H.
intros m'g H; elim H; clear H.
intros H_col1 H; elim H; clear H.
intros H_col2 H_col3.
exists (c_state (hp s) m' mark).
apply c_fstep with (a := label_mark); unfold fair in |- *; auto.
constructor; constructor; auto.
apply grey_node with (g := g); auto.
intros n H; elim H; clear H.
intros ndifg H; elim H; clear H.
intro H; elim H; clear H.
intros hsgn mksn; symmetry  in |- *; apply H_col2; auto.
intros hsgn; symmetry  in |- *; apply H_col3; auto.
Qed.

Hint Resolve marknode_fair.

Lemma gcfree_fair :
 forall s : state,
 ctl s = mark ->
 (forall n : node, mk s n <> grey) ->
 (exists n : node, mk s n = white) ->
 exists t : state,
   fair_step (fun (a : label) (s t : state) => transition s t a) fair s t. 

intros s ctls H_col H_white; elim H_white; clear H_white.
intros n mksn; cut (exists m' : marking, update_color (mk s) m' free n);
 eauto.
intro H_m'; elim H_m'; clear H_m'.
intros mk' upd_col; exists (c_state (hp s) mk' sweep).
apply c_fstep with (a := label_free); unfold fair in |- *; auto.
constructor; apply free_no_grey_but_white with (m := n); auto.
Qed.

Hint Resolve gcfree_fair.

Lemma free1_white_fair :
 forall s : state,
 ctl s = sweep ->
 (exists n : node, mk s n = white) ->
 exists t : state,
   fair_step (fun (a : label) (s t : state) => transition s t a) fair s t. 

intros s ctls H_white; elim H_white; clear H_white.
intros n mksn; cut (exists m' : marking, update_color (mk s) m' free n);
 eauto.
intro H_m'; elim H_m'; clear H_m'.
intros mk' upd_col.
exists (c_state (hp s) mk' sweep).
apply c_fstep with (a := label_free1); unfold fair in |- *; auto.
constructor.
apply free1_white with (n := n); auto.
Qed.

Hint Resolve free1_white_fair.

Axiom
  exist_or_none :
    forall (c : color) (m : marking),
    {(forall n : node, m n <> c)} + {(exists n : node, m n = c)}.

Lemma always_exist_fairstep :
 forall s : state,
 sweep_no_greys s ->
 (exists nb : nat, mesure (mk s) nb /\ nb <> 0) ->
 exists t : state,
   fair_step (fun (a : label) (s t : state) => transition s t a) fair s t.

unfold sweep_no_greys in |- *; intros s inv mes_s; elim mes_s; clear mes_s.
intros nb H; elim H; clear H.
intros mes_s nbdifO.
generalize (refl_equal (ctl s)); pattern (ctl s) at -1 in |- *; case (ctl s);
 intro ctls.
elim (exist_or_none grey (mk s)); eauto.
intro H_col; elim (exist_or_none white (mk s)); eauto.
elim (exist_or_none grey (mk s)); eauto.
intro H_col; elim (exist_or_none white (mk s)); eauto.
intro H_col2; cut (exists nb' : nat, mesure (mk s) nb' /\ nb' = 0).
intro H; elim H; clear H.
intros nb' H_nb'; elim H_nb'; clear H_nb'.
intros H_mes' nb'eqO; absurd (nb' = 0); auto.
cut (nb = nb').
intro nbeqnb'; rewrite <- nbeqnb'; assumption.
apply measure_unicity with (m := mk s); assumption.
exists 0; split; auto.
replace 0 with (0 + 0); auto with arith.
constructor; constructor; auto.
elim (exist_or_none white (mk s)); eauto.
intro H_col; cut (exists nb' : nat, mesure (mk s) nb' /\ nb' = 0).
intro H; elim H; clear H.
intros nb' H_nb'; elim H_nb'; clear H_nb'.
intros H_mes' nb'eqO; absurd (nb' = 0); auto.
cut (nb = nb').
intro nbeqnb'; rewrite <- nbeqnb'; assumption.
apply measure_unicity with (m := mk s); assumption.
exists 0; split; auto.
replace 0 with (0 + 0); auto with arith.
constructor; constructor; auto.
Qed.

Hint Resolve always_exist_fairstep.

Lemma always_fairstep :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
 ((exists s : state,
     fair_step (fun (a : label) (s t : state) => transition s t a) fair
       (head_str str) s) ->
  fair_step (fun (a : label) (s t : state) => transition s t a) fair
    (head_str str) (head_str (tl_str str))) ->
 fair_step (fun (a : label) (s t : state) => transition s t a) fair
   (head_str str) (head_str (tl_str str)).

intros str H_sweep mes_str H; inversion H_sweep.
rewrite H2; rewrite H2 in H0.
clear H1 H2; apply H; apply always_exist_fairstep; auto.
Qed.

Hint Resolve always_fairstep.

Lemma infinitely_fairstep :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 infinitely_often
   (fun str : stream state =>
    (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
    fair_step (fun (a : label) (s t : state) => transition s t a) fair
      (head_str str) (head_str (tl_str str))) str.

unfold fairstr in |- *; intros str H_always H_infinitely.
apply
 inv_implies_inf_often
  with
    (P := fun str : stream state =>
          enabled
            (fair_step (fun (a : label) (s t : state) => transition s t a)
               fair) (head_str str) ->
          fair_step (fun (a : label) (s t : state) => transition s t a) fair
            (head_str str) (head_str (tl_str str)))
    (I := state2stream_formula (fun s : state => sweep_no_greys s)); 
 auto.
clear H_infinitely H_always str.
intros str H_always H_enabled H_mes.
inversion H_always; rewrite H1 in H; rewrite H1; clear H0 H1 str0 s0.
apply H_enabled;
 cut
  (exists s : state,
     fair_step (fun (a : label) (s0 t : state) => transition s0 t a) fair
       (head_str str) s); eauto.
intro H_exist; elim H_exist.
intros s H_fair.
apply c_pos_trans with (t := s); assumption.
Qed.

Hint Resolve infinitely_fairstep.

Lemma fairstr_eventually :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 Eventually
   (fun str : stream state =>
    (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
    fair_step (fun (a : label) (s t : state) => transition s t a) fair
      (head_str str) (head_str (tl_str str))) str.

intros str H_always H_fairstr.
cut
 (infinitely_often
    (fun str : stream state =>
     (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
     fair_step (fun (a : label) (s t : state) => transition s t a) fair
       (head_str str) (head_str (tl_str str))) str); 
 eauto.
intro H_infinitely; inversion H_infinitely; assumption.
Qed.

Lemma fairstr_eventually_tl :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 Eventually
   (fun str : stream state =>
    (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
    fair_step (fun (a : label) (s t : state) => transition s t a) fair
      (head_str str) (head_str (tl_str str))) (tl_str str).

intros str H_always H_fairstr.
cut
 (infinitely_often
    (fun str : stream state =>
     (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
     fair_step (fun (a : label) (s t : state) => transition s t a) fair
       (head_str str) (head_str (tl_str str))) str); 
 eauto.
intro H_infinitely; inversion H_infinitely.
generalize H0 H; clear H0 H.
rewrite H1; replace str0 with (tl_str str).
2: rewrite <- H1; auto.
clear H1 str0 s0.
intros H_always_ev H_eventually; inversion H_always_ev; assumption.
Qed.

End fairstr.









