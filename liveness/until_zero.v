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
(*                              until_zero.v                                *)
(****************************************************************************)

Section until_zero.

Require Export mesure.
Require Export well_founded.
Require Export Wf_nat.
Require Export unicite_mes.
Require Export fairstr.
Require Export safe_card.

Hint Resolve lt_wf.

Notation Stream := (stream state) (only parsing).
Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Fair_step :=
  (fair_step (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).
Notation Run :=
  (run init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Fairstr :=
  (fairstr (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).
(*
Syntactic Definition Fair_step:=(fair_step [a:label; s,t :state](transition s t a) fair).
*)
Notation Once_always := (once_always state) (only parsing).
Notation Wf_leadsto_rule := (wf_leadsto_rule nat state) (only parsing).
Notation State_formula := (state_formula state) (only parsing).
Notation Trace := (trace (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation None_or_one_step :=
  (none_or_one_step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).

Definition measure (s : state) (nb : nat) : Prop := mesure (mk s) nb.

Definition positive_measure : state_formula state :=
  fun s => exists nb : nat, measure s nb /\ nb <> 0.

Lemma fairness_decrease :
 forall s t : state,
 fair_step (fun (a : label) (s t : state) => transition s t a) fair s t ->
 forall v : nat, measure s v /\ v <> 0 -> measure t (pred v).

intros s t H_fair v H_v; elim H_v; clear H_v.
unfold measure in |- *; intros H_mes vdifO; inversion_clear H_fair.
generalize (refl_equal a); pattern a at -1 in |- *; case a; intro H_a.
absurd (fair a); auto.
rewrite H_a; simpl in |- *; auto.
absurd (fair a); auto.
rewrite H_a; simpl in |- *; auto.
absurd (fair a); auto.
rewrite H_a; simpl in |- *; auto.
rewrite H_a in H0; inversion_clear H0.
cut
 (mesure (mk s) 0 \/ (mesure (mk s) v -> v <> 0 /\ mesure (mk t) (pred v)));
 eauto.
intro Hmes; elim Hmes; clear Hmes.
intro Hmes; absurd (exists nb : nat, mesure (mk s) nb /\ nb = 0).
intro H2; elim H2; clear H2.
intros nb H_nb; elim H_nb; clear H_nb.
intros H_mes_nb nbeqO; absurd (nb = 0); auto.
cut (nb = v);
 [ intro nbeqv; rewrite nbeqv; assumption
 | apply measure_unicity with (m := mk s); assumption ].
exists 0; auto.
intro Hmes; elim Hmes; clear Hmes; auto.
rewrite H_a in H0; inversion_clear H0.
cut (mesure (mk t) (pred v)); eauto.
absurd (fair a); auto.
rewrite H_a; simpl in |- *; auto.
rewrite H_a in H0; inversion_clear H0; eauto.
rewrite H_a in H0; inversion_clear H0; eauto.
absurd (fair a); auto.
rewrite H_a; simpl in |- *; auto.
Qed.

Hint Resolve fairness_decrease.

Lemma fairness_lt :
 forall s t : state,
 fair_step (fun (a : label) (s t : state) => transition s t a) fair s t ->
 forall v : nat,
 measure s v /\ v <> 0 -> exists nb : nat, measure t nb /\ nb < v.

intros s t H_fair v H_mes; exists (pred v); split; eauto.
elim H_mes; clear H_mes.
intros H_mes vdif0; apply (lt_pred_n_n v); apply (neq_O_lt v); auto.
Qed.

Hint Resolve fairness_lt.

Lemma step_decrease :
 forall (s t : state) (nb : nat),
 measure s nb /\ nb <> 0 ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 exists nb' : nat, measure t nb' /\ nb' <= nb.

unfold measure in |- *; intros s t nb H step; elim H; clear H.
intros H_mes nbdif0.
cut
 (mesure (mk s) 0 \/
  (nb <> 0 /\ mesure (mk s) nb -> mesure (mk t) nb \/ mesure (mk t) (pred nb)));
 eauto.
intros H; elim H; clear H.
intro Hmes; absurd (exists nb : nat, mesure (mk s) nb /\ nb = 0);
 [ intro H; elim H; clear H | exists 0; split; auto ].
intros nb' H; elim H; clear H.
intros Hmes_nb' nb'eq0; absurd (nb' = 0); auto.
cut (nb' = nb).
intro nb'eqnb; rewrite nb'eqnb; assumption.
apply measure_unicity with (m := mk s); assumption.
intro H; elim H; clear H.
intro Hmes; exists nb; split; auto.
intro Hmes; exists (pred nb); split; auto.
auto with arith.
split; auto.
Qed.

Hint Resolve step_decrease.

Lemma none_or_one_decrease :
 forall (s t : state) (nb : nat),
 measure s nb /\ nb <> 0 ->
 none_or_one_step (fun (a : label) (s t : state) => transition s t a) s t ->
 exists nb' : nat, measure t nb' /\ nb' <= nb.

intros s t nb H H_step; inversion H_step; eauto.
rewrite <- H0; exists nb; split; auto.
elim H; auto.
Qed.

Hint Resolve none_or_one_decrease.

Lemma measure_trivial :
 forall (s : state) (nb : nat),
 positive_measure s /\ measure s nb -> measure s nb /\ nb <> 0.

intros s nb H; elim H; clear H.
intros H H_mes; elim H; clear H.
intros nb' H; elim H; clear H.
intros H_mes' nb'dif0; split; auto.
cut (nb = nb').
intro nbeqnb'; rewrite nbeqnb'; assumption.
apply measure_unicity with (m := mk s); auto.
Qed.

Hint Resolve measure_trivial.

Lemma measure_trivial_bis :
 forall (s : state) (nb v : nat),
 positive_measure s /\ (exists nb : nat, measure s nb /\ nb < v) ->
 exists nb : nat, measure s nb /\ nb < v /\ nb <> 0.

intros s nb v H; elim H; clear H.
intros H H'; elim H; elim H'; clear H H'.
intros nb' H v' H'; elim H; elim H'; clear H H'.
intros meas_v' v'difO meas_nb' lt_nb'_v.
cut (nb' = v');
 [ intro nb'eqv' | apply measure_unicity with (m := mk s); auto ].
rewrite <- nb'eqv' in v'difO; exists nb'; split; auto.
Qed.

Hint Resolve measure_trivial_bis.

Remark le_measure :
 forall v w : nat,
 w <= v ->
 forall s : state,
 (exists nb : nat, measure s nb /\ nb < w) ->
 exists nb : nat, measure s nb /\ nb < v.

intros v w le_w_v s H; elim H; clear H.
intros nb H; elim H; clear H.
intros H_mes lt_nb_w; exists nb; split; auto.
apply (lt_le_trans nb w v); auto.
Qed.

Hint Resolve le_measure.

Lemma and_exist :
 forall (s : state) (tl : stream state) (v : nat),
 state2stream_formula (fun s : state => positive_measure s /\ measure s v)
   (cons_str s tl) ->
 state2stream_formula
   (fun s0 : state => positive_measure s0 /\ (exists nb : nat, measure s0 nb))
   (cons_str s tl).

unfold state2stream_formula in |- *; simpl in |- *; intros s tl v H; elim H;
 clear H.
intros H_pos H_mes; split; auto.
exists v; assumption.
Qed.

Hint Resolve and_exist.

Lemma trivial_unicity :
 forall (s : state) (v w : nat),
 measure s v -> measure s w -> w <> 0 -> measure s v /\ v <> 0.

intros s v w H_v H_w wdifO; split; auto.
cut (v = w);
 [ intro veqw; rewrite veqw; assumption
 | apply measure_unicity with (m := mk s); auto ].
Qed.

Hint Resolve trivial_unicity.

Lemma trivial_unicity_bis :
 forall (s : state) (tl : stream state) (v : nat),
 state2stream_formula (fun s : state => positive_measure s /\ measure s v)
   (cons_str s tl) -> exists nb : nat, mesure (mk s) nb /\ nb <> 0.

unfold state2stream_formula in |- *; simpl in |- *; intros s tl v H; elim H;
 clear H.
intros H H_mes; elim H; clear H.
intros w H; elim H; clear H.
intros Hmes wdifO; exists w; split; assumption.
Qed.

Hint Resolve trivial_unicity_bis.

Lemma until_zero :
 forall str : stream state,
 Eventually
   (fun str : stream state =>
    (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
    fair_step (fun (a : label) (s t : state) => transition s t a) fair
      (head_str str) (head_str (tl_str str))) str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 forall v : nat,
 state2stream_formula (fun s : state => positive_measure s /\ measure s v)
   str ->
 until
   (state2stream_formula
      (fun s0 : state =>
       positive_measure s0 /\ (exists nb : nat, measure s0 nb)))
   (state2stream_formula
      (fun s0 : state =>
       positive_measure s0 /\ (exists nb : nat, measure s0 nb /\ nb < v) \/
       measure s0 0)) str.

simple induction 1; clear H str.
intro str; generalize (refl_equal str); pattern str at -1 in |- *; case str.
intros s tl H_str H_fair H_trace v H_mes.
constructor 2; eauto.
constructor 1.
unfold state2stream_formula in |- *; simpl in |- *.
cut
 (fair_step (fun (a : label) (s t : state) => transition s t a) fair
    (head_str (cons_str s tl)) (head_str (tl_str (cons_str s tl)))).
intro H_fairstep; replace tl with (tl_str str).
2: rewrite H_str; auto.
elim H_mes; clear H_mes.
unfold positive_measure in |- *; intros H_pos H_mes; elim H_pos; clear H_pos.
intros nb Hmes; elim Hmes; clear Hmes.
intros Hmes nbdifO.
cut (exists nb : nat, measure (head_str (tl_str str)) nb /\ nb < v);
 [ intro Hmes_hd; elim Hmes_hd; clear Hmes_hd
 | apply fairness_lt with (s := head_str (cons_str s tl));
    replace str with (cons_str s tl); auto ]; eauto.
intros nb' Hmes_nb'.
elim Hmes_nb'; clear Hmes_nb'.
intros Hmes_nb' lt_nb'_v.
elim (eq_nat_dec nb' 0);
 [ intro nb'eqO; rewrite nb'eqO in Hmes_nb'; right; assumption
 | intro nb'difO; left; split;
    [ exists nb'; split; assumption | exists nb'; split; assumption ] ].
apply H_fair; eauto.
intros s str H_ev H_ind H_trace v H_mes.
constructor 2; eauto.
cut (exists w : nat, measure (head_str str) w /\ w <= v);
 [ intro H; elim H; clear H
 | inversion H_trace; clear H2 H0 H s0 str0; simpl in H1;
    apply none_or_one_decrease with (s := s); auto ].
intros w H; elim H; clear H.
intros Hmes le_w_v; elim (eq_nat_dec w 0);
 [ intro weqO; rewrite weqO in Hmes; constructor 1;
    unfold state2stream_formula in |- *; right; assumption
 | intro nbdifO; inversion H_trace; simpl in H1; inversion H1;
    clear H2 H1 H0 H s0 str0 ].
apply H_ind;
 [ inversion H_trace; assumption
 | unfold state2stream_formula in |- *; unfold state2stream_formula in H_mes;
    simpl in H_mes; rewrite <- H3; assumption ].
apply
 until_implies_until_stream
  with
    (P := state2stream_formula
            (fun s0 : state =>
             positive_measure s0 /\ (exists nb : nat, measure s0 nb)))
    (Q := state2stream_formula
            (fun s0 : state =>
             positive_measure s0 /\
             (exists nb : nat, measure s0 nb /\ nb < w) \/ 
             measure s0 0)); eauto.
unfold state2stream_formula in |- *; simpl in |- *; eauto.
intros str' H; elim H; clear H.
intro H; elim H; clear H.
intros H_pos H_ex; left; split; eauto.
right; assumption.
apply H_ind; [ inversion H_trace; assumption | auto ].
unfold state2stream_formula in |- *; split; auto.
unfold positive_measure in |- *; exists w; split; assumption.
Qed.

Hint Resolve until_zero.

Lemma once_until_zero :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 once_until
   (state2stream_formula
      (fun s : state => positive_measure s /\ (exists nb : nat, measure s nb)))
   (state2stream_formula (fun s : state => measure s 0)) str.

unfold once_until in |- *; intros str H_always H_fair H_trace;
 apply (wf_leadsto_rule nat state) with (r := lt); 
 eauto.
unfold leads_to_via in |- *; unfold implies in |- *.
generalize str H_fair H_always H_trace; clear H_fair H_always H_trace str;
 cofix.
unfold fairstr in |- *; unfold infinitely_often in |- *; intro str; case str;
 clear str.
intros s str H_fair H_always H_trace v; constructor;
 [ clear once_until_zero
 | inversion H_always; inversion H_fair; inversion H_trace;
    apply once_until_zero; assumption ].
cut
 (Eventually
    (fun str : stream state =>
     (exists nb : nat, mesure (mk (head_str str)) nb /\ nb <> 0) ->
     fair_step (fun (a : label) (s t : state) => transition s t a) fair
       (head_str str) (head_str (tl_str str))) (cons_str s str)).
intros H_ev H_mes; eauto.
apply fairstr_eventually; auto.
Qed.

Hint Resolve once_until_zero.

Lemma measure_until_zero :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 once_until (state2stream_formula (fun s : state => positive_measure s))
   (state2stream_formula (fun s : state => measure s 0)) str.

intros str H_always H_fair H_trace.
apply
 once_equiv_once
  with
    (A := state2stream_formula
            (fun s : state =>
             positive_measure s /\ (exists nb : nat, measure s nb))); 
 eauto; clear H_fair H_always H_trace str.
intros str H; elim H; clear H.
intros H_pos H_mes; unfold state2stream_formula in |- *.
simpl in |- *; assumption.
intros str H; elim H; clear H.
intros v H; elim H; clear H.
intros H_mes vdif0.
unfold state2stream_formula in |- *; simpl in |- *; split.
unfold positive_measure in |- *; exists v; split; assumption.
exists v; assumption.
Qed.

Hint Resolve measure_until_zero.

Lemma measure_until_zero_on_run :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 once_until (state2stream_formula (fun s : state => positive_measure s))
   (state2stream_formula (fun s : state => measure s 0)) str.

intros str H_run H_fair;
 cut (always (state2stream_formula (fun s : state => sweep_no_greys s)) str);
 eauto.
intro H_always; inversion H_run; eauto.
Qed.

Hint Resolve measure_until_zero_on_run. 

Lemma eventually_measure_until_zero_trace :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 positive_measure (head_str str) ->
 Eventually (state2stream_formula (fun s : state => measure s 0)) str.

intros str H_always H_fair H_run H_pos.
apply
 once_eventually
  with (P := state2stream_formula (fun s : state => positive_measure s));
 eauto.
Qed.

Hint Resolve eventually_measure_until_zero_trace.

Lemma eventually_measure_until_zero :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 positive_measure (head_str str) ->
 Eventually (state2stream_formula (fun s : state => measure s 0)) str.

intros str H_run H_fair H_pos.
apply
 once_eventually
  with (P := state2stream_formula (fun s : state => positive_measure s));
 eauto.
Qed.

Hint Resolve eventually_measure_until_zero.

Lemma eventually_measure_until_zero_trace_bis :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb))
   str ->
 Eventually (state2stream_formula (fun s : state => measure s 0)) str.

intros str H_always_sweep H_fairstr H_trace H_always; inversion H_always.
rewrite H1 in H; rewrite H1; clear H0 H1; unfold state2stream_formula in H;
 simpl in H.
elim H; clear H.
intros nb H_mes; elim (eq_nat_dec nb 0).
intro nbeq0; rewrite nbeq0 in H_mes; constructor 1; assumption.
intro nbdif0; apply eventually_measure_until_zero_trace; auto.
unfold positive_measure in |- *; exists nb; split; assumption.
Qed.

Hint Resolve eventually_measure_until_zero_trace_bis.

Lemma eventually_measure_until_zero_on_run :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 Eventually (state2stream_formula (fun s : state => measure s 0)) str.

intros str H_run H_fairstr.
cut
 (always
    (state2stream_formula
       (fun s : state => exists nb : nat, mesure (mk s) nb)) str); 
 eauto.
intro H_always; inversion H_always.
rewrite H1 in H; rewrite H1; clear H0 H1; unfold state2stream_formula in H;
 simpl in H.
elim H; clear H.
intros nb H_mes; elim (eq_nat_dec nb 0).
intro nbeq0; rewrite nbeq0 in H_mes; constructor 1; assumption.
intro nbdif0; apply eventually_measure_until_zero; auto.
unfold positive_measure in |- *; exists nb; split; assumption.
Qed.

Hint Resolve eventually_measure_until_zero_on_run.

Lemma measureO_greyO :
 forall str : stream state,
 state2stream_formula (fun s : state => measure s 0) str ->
 state2stream_formula (fun s : state => card_color grey (mk s) 0) str.

unfold state2stream_formula in |- *; simpl in |- *; intros str H; inversion H;
 clear H.
rewrite H0; cut (g = 0).
intro geqO; rewrite <- geqO; assumption.
rewrite (plus_comm g w) in H0.
apply (plus_O_O w g); assumption.
Qed.

Hint Resolve measureO_greyO.

Lemma measureO_whiteO :
 forall str : stream state,
 state2stream_formula (fun s : state => measure s 0) str ->
 state2stream_formula (fun s : state => card_color white (mk s) 0) str.

unfold state2stream_formula in |- *; simpl in |- *.
intros str H; inversion H; clear H.
rewrite H0; cut (w = 0).
intro weqO; rewrite <- weqO; assumption.
apply (plus_O_O g w); assumption.
Qed.

Hint Resolve measureO_whiteO.

Lemma eventually_grey_until_zero_trace :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb))
   str ->
 Eventually
   (state2stream_formula (fun s : state => card_color grey (mk s) 0)) str.

intros str H_always_sweep H_fair H_trace H_always.
apply
 eventually_implies_eventually
  with (P := state2stream_formula (fun s : state => measure s 0)); 
 eauto.
Qed.

Hint Resolve eventually_grey_until_zero_trace.

Lemma always_eventually_grey_until_zero_trace :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb))
   str ->
 always
   (Eventually
      (state2stream_formula (fun s : state => card_color grey (mk s) 0))) str.

unfold trace in |- *; unfold fairstr in |- *; unfold infinitely_often in |- *;
 cofix.
intro str; case str; clear str.
intros s str H_always_sweep H_fair H_trace H_always; constructor; eauto.
inversion H_always_sweep; inversion H_fair; inversion H_trace;
 inversion H_always.
apply always_eventually_grey_until_zero_trace; assumption.
Qed.

Lemma eventually_grey_until_zero :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 Eventually
   (state2stream_formula (fun s : state => card_color grey (mk s) 0)) str.

intros str H_run H_fair.
apply
 eventually_implies_eventually
  with (P := state2stream_formula (fun s : state => measure s 0)); 
 eauto.
Qed.

Hint Resolve eventually_grey_until_zero.

Lemma eventually_white_until_zero_trace :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb))
   str ->
 Eventually
   (state2stream_formula (fun s : state => card_color white (mk s) 0)) str.

intros str H_always_sweep H_fair H_trace H_always.
apply
 eventually_implies_eventually
  with (P := state2stream_formula (fun s : state => measure s 0)); 
 eauto.
Qed.

Hint Resolve eventually_white_until_zero_trace.

Lemma always_eventually_white_until_zero_trace :
 forall str : stream state,
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb))
   str ->
 always
   (Eventually
      (state2stream_formula (fun s : state => card_color white (mk s) 0)))
   str.

unfold trace in |- *; unfold fairstr in |- *; unfold infinitely_often in |- *;
 cofix.
intro str; case str; clear str.
intros s str H_always_sweep H_fair H_trace H_always; constructor; eauto.
inversion H_always_sweep; inversion H_fair; inversion H_trace;
 inversion H_always.
apply always_eventually_white_until_zero_trace; assumption.
Qed.

Lemma eventually_white_until_zero :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 Eventually
   (state2stream_formula (fun s : state => card_color white (mk s) 0)) str.

intros str H_run H_fair.
apply
 eventually_implies_eventually
  with (P := state2stream_formula (fun s : state => measure s 0)); 
 eauto.
Qed.

Hint Resolve eventually_white_until_zero.

End until_zero.

Hint Resolve always_eventually_grey_until_zero_trace.
Hint Resolve always_eventually_white_until_zero_trace.
