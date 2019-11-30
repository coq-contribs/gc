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
(*                             Septembre 2001                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 LTL.v                                    *)
(****************************************************************************)

Section LTL.

Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.

(**************************** Parameters ************************************)

Variables (state : Set) (label : Set) (init_state : state -> Prop)
  (transition : label -> relation state) (fair : label -> Prop). 

Inductive step (s t : state) : Prop :=
    C_trans : forall a : label, transition a s t -> step s t.

Inductive enabled (r : relation state) (s : state) : Prop :=
    c_pos_trans : forall t : state, r s t -> enabled r s.

Inductive none_or_one_step (s : state) : state -> Prop :=
  | none : none_or_one_step s s
  | one : forall t : state, step s t -> none_or_one_step s t.

Definition state_formula := state -> Prop. 

(********************************** Streams *********************************)

CoInductive stream : Set :=
    cons_str : state -> stream -> stream.

Definition head_str (str : stream) : state :=
  match str with
  | cons_str s _ => s
  end.

Definition tl_str (str : stream) : stream :=
  match str with
  | cons_str _ tl => tl
  end.

Definition stream_formula := stream -> Prop.

Definition state2stream_formula (P : state_formula) : stream_formula :=
  fun str : stream => P (head_str str).

Definition and (P Q : stream_formula) : stream_formula :=
  fun str : stream => P str /\ Q str.

Definition and_state (P Q : state_formula) : state_formula :=
  fun s : state => P s /\ Q s.

Definition leads_to (P Q : state_formula) : Prop :=
  forall s t : state, P s -> step s t -> Q t.

(****************************** LTL basic operators *************************)

Definition next (P : stream_formula) : stream_formula :=
  fun str => P (tl_str str).

CoInductive always (P : stream_formula) : stream -> Prop :=
    C_always :
      forall (s0 : state) (str : stream),
      P (cons_str s0 str) -> always P str -> always P (cons_str s0 str).

Definition trace : stream -> Prop :=
  always
    (fun str : stream =>
     none_or_one_step (head_str str) (head_str (tl_str str))).
            
Definition run (str : stream) : Prop :=
  init_state (head_str str) /\ trace str.

Inductive Eventually (P : stream_formula) : stream -> Prop :=
  | ev_h : forall str : stream, P str -> Eventually P str
  | ev_t :
      forall (s : state) (str : stream),
      Eventually P str -> Eventually P (cons_str s str).

Inductive until (P Q : stream_formula) : stream -> Prop :=
  | until_h : forall str : stream, Q str -> until P Q str
  | until_t :
      forall (s : state) (str : stream),
      P (cons_str s str) -> until P Q str -> until P Q (cons_str s str).

CoInductive unless (P Q : stream_formula) : stream -> Prop :=
  | unless_h : forall str : stream, Q str -> unless P Q str
  | unless_t :
      forall (s : state) (str : stream),
      P (cons_str s str) -> unless P Q str -> unless P Q (cons_str s str).


(****************************** LTL derived operators ***********************)

Definition infinitely_often (P : stream_formula) : 
  stream -> Prop := always (Eventually P).

Definition implies (P Q : stream_formula) : stream -> Prop :=
  always (fun str : stream => P str -> Q str).

Definition is_followed (P Q : stream_formula) (str : stream) : Prop :=
  P str -> Eventually Q str.

Definition is_always_followed (P Q : stream_formula) : 
  stream -> Prop := always (is_followed P Q).

Definition Eventually_permanently (P : stream_formula) : 
  stream -> Prop := Eventually (always P).

Definition once_always (P Q : stream_formula) : stream -> Prop :=
  always (fun str : stream => P str -> always Q str).

Definition leads_to_via (P Q R : stream_formula) : 
  stream -> Prop := implies P (until Q R).

Definition once_until (P Q : stream_formula) : stream -> Prop :=
  leads_to_via P P Q.

(********************************** Fairness ********************************)

Definition fairness (a : label) (str : stream) : Prop :=
  infinitely_often (state2stream_formula (enabled (transition a))) str ->
  Eventually
    (fun str : stream => transition a (head_str str) (head_str (tl_str str)))
    str.

Inductive fair_step (s1 s2 : state) : Prop :=
    c_fstep :
      forall a : label, fair a -> transition a s1 s2 -> fair_step s1 s2.

Definition fairstr : stream -> Prop :=
  infinitely_often
    (fun str =>
     enabled fair_step (head_str str) ->
     fair_step (head_str str) (head_str (tl_str str))).

Definition strong_fairstr (str : stream) : Prop :=
  always
    (Eventually
       (fun str' => fair_step (head_str str') (head_str (tl_str str')))) str.
     
(************************************  Safety *******************************)

Definition invariant (P : state_formula) : Prop := leads_to P P.

Definition safe (P : stream_formula) :=
  forall str : stream, run str -> always P str.

(************************************  Lemmas *******************************)

Lemma once_eventually :
 forall (P Q : stream_formula) (str : stream),
 once_until P Q str -> P str -> Eventually Q str.

unfold once_until in |- *; unfold leads_to_via in |- *;
 unfold implies in |- *.
intros P Q str H_always H_P; inversion H_always.
rewrite H1; rewrite H1 in H; clear H0 H1 str0 s0.
elim H; auto.
clear H H_P H_always str; intros str H_Q; constructor 1; assumption.
clear H H_P H_always str; intros s str H_P H_until H_ev; constructor 2;
 assumption.
Qed.

Lemma eventually_implies_eventually :
 forall (P Q : stream_formula) (str : stream),
 Eventually P str ->
 (forall str : stream, P str -> Q str) -> Eventually Q str.

simple induction 1; clear H str;
 [ intros str H_P H_P_Q; constructor 1; apply H_P_Q; assumption
 | intros s str H_ev H_ind H_P_Q; constructor 2; apply H_ind; assumption ].
Qed.

Lemma until_implies_until_stream :
 forall P P' Q Q' : stream_formula,
 (forall str : stream, P str -> P' str) ->
 (forall str : stream, Q str -> Q' str) ->
 forall str : stream, until P Q str -> until P' Q' str.

intros P P' Q Q' H_P_P' H_Q_Q'.
simple induction 1; clear H str.
intros str H_Q; constructor 1; apply H_Q_Q'; assumption.
intros s str H_P H_until H_until'; constructor 2; auto.
Qed.

Lemma until_implies_until_state :
 forall P P' Q Q' : state_formula,
 (forall s : state, P s -> P' s) ->
 (forall s : state, Q s -> Q' s) ->
 forall str : stream,
 until (state2stream_formula P) (state2stream_formula Q) str ->
 until (state2stream_formula P') (state2stream_formula Q') str.

intros P P' Q Q' H_P_P' H_Q_Q'.
simple induction 1; clear H str.
intro str; case str; clear str.
unfold state2stream_formula in |- *; simpl in |- *; intros s str H_Q;
 constructor 1; simpl in |- *; apply H_Q_Q'; assumption.
unfold state2stream_formula in |- *; intros s str H_P H_until H_until';
 constructor 2; auto.
Qed.
        

Lemma always_on_run :
 forall F P I : stream_formula,
 safe I ->
 (forall str : stream, trace str -> always F str -> always I str -> P str) ->
 forall str : stream, run str -> always F str -> always P str.

unfold safe in |- *; unfold run in |- *; intros F P I H_safe H str str_safe;
 elim str_safe.
intro h; clear h; cut (always I str); auto.
clear str_safe; generalize str; clear str H_safe.
cofix always_on_run.
intro str; case str; clear str.
intros s str always_I H_trace always_F; inversion always_I; inversion H_trace;
 inversion always_F; constructor.
2: apply always_on_run; auto. 
apply H; auto.
Qed.

Lemma implies_inf_often :
 forall P Q : stream_formula,
 (forall str : stream, P str -> Q str) ->
 forall str : stream, infinitely_often P str -> infinitely_often Q str.

unfold infinitely_often in |- *; intros P Q H_P_Q; cofix implies_inf_often; intro str; case str;
 clear str.
intros s str H_always; constructor;
 [ clear implies_inf_often
 | apply implies_inf_often; inversion H_always; auto ].
inversion H_always.
clear H H0 s0 str0.
generalize H_always; elim H1; clear H2 H1 H_always str s.
intros str H_P H_always; constructor 1; apply H_P_Q; assumption.
intros s str H_eventually H_rec H_always; constructor 2; apply H_rec;
 inversion H_always; assumption.
Qed.

Lemma inv_implies_inf_often :
 forall P Q I : stream_formula,
 (forall str : stream, always I str -> P str -> Q str) ->
 forall str : stream,
 always I str -> infinitely_often P str -> infinitely_often Q str.

unfold infinitely_often in |- *; intros P Q I H_P_Q; cofix inv_implies_inf_often; intro str;
 case str; clear str.
intros s str H_always_I H_always_ev; constructor;
 [ clear inv_implies_inf_often
 | apply inv_implies_inf_often; inversion H_always_I; inversion H_always_ev;
    auto ].
inversion H_always_ev.
clear H H0 s0 str0.
generalize H_always_ev H_always_I; elim H1;
 clear H2 H1 H_always_ev H_always_I str s.
intros str H_P H_always_ev H_always_I; constructor 1; apply H_P_Q; assumption.
intros s str H_eventually H_rec H_always_ev H_always_I; constructor 2;
 apply H_rec; inversion H_always_ev; inversion H_always_I; 
 assumption.
Qed.

Lemma one_step_leads_to :
 forall P Q : state_formula,
 (forall s : state, P s -> enabled fair_step s) ->
 leads_to P Q ->
 forall str : stream,
 trace str ->
 fairstr str ->
 state2stream_formula P str ->
 until (state2stream_formula P) (state2stream_formula Q) str.

unfold fairstr in |- *; unfold infinitely_often in |- *;
 unfold leads_to in |- *.
intros P Q H_enabled leads_P_Q str H_trace H_fair H_P; generalize H_trace H_P;
 inversion_clear H_fair; clear H_trace H_P H0; elim H; 
 clear H.
clear str s0 str0; intro str; case str. 
clear str; intros s str H_fair H_trace H_P; constructor 2; auto.
constructor 1; unfold state2stream_formula in |- *;
 apply leads_P_Q with (s := s); auto.
elim H_fair.
intros a fair_a H_trans; clear fair_a; apply C_trans with (a := a); auto.
apply H_enabled; auto.
unfold state2stream_formula in |- *; simpl in |- *;
 intros s1 str1 H_ind H1 H_trace H_P; inversion_clear H_trace; 
 inversion H.
constructor 2; auto.
apply H1; auto.
simpl in H2; rewrite <- H2; assumption.
simpl in H2; constructor 2; auto.
constructor 1; apply leads_P_Q with (s := s1); trivial.
Qed.

Hint Resolve one_step_leads_to.

Lemma always_one_step_leads_to :
 forall P Q : state_formula,
 (forall s : state, P s -> enabled fair_step s) ->
 leads_to P Q ->
 forall str : stream,
 trace str ->
 fairstr str ->
 leads_to_via (state2stream_formula P) (state2stream_formula P)
   (state2stream_formula Q) str.

unfold leads_to_via in |- *; unfold implies in |- *;
 intros P Q H_enabled leads_P_Q; cofix always_one_step_leads_to.
intro str; case str; intros s str'; case str'.
intros t tl H_trace H_fair; constructor; eauto.
inversion_clear H_trace; inversion_clear H_fair;
 apply always_one_step_leads_to; auto.
Qed.

Lemma until_or :
 forall (A B C D E : stream_formula) (str : stream),
 leads_to_via A B C str ->
 (C str -> until D E str) ->
 C str -> until (fun str : stream => B str \/ D str) E str.

intros A B C D E str H_always H_until H_C.
elim (H_until H_C); clear H_always H_until H_C str.
intros str H_E; constructor 1; assumption.
intros s str H_D until_D_E until_or; constructor 2; auto.
Qed.

Hint Resolve until_or.

Lemma until_trans :
 forall (A B C D E : stream_formula) (str : stream),
 (A str -> until B C str) ->
 leads_to_via C D E str ->
 A str -> until (fun str : stream => B str \/ D str) E str.

intros A B C D E str H_until H_always H_A; generalize H_always;
 clear H_always; unfold leads_to_via in |- *; unfold implies in |- *;
 elim (H_until H_A); clear H_until H_A str.
intros str H_C H_always; inversion H_always.
rewrite H1 in H; rewrite H1; elim (H H_C);
 clear H H0 H1 s0 str0 H_always H_C str.
intros str E_str; constructor 1; assumption.
intros s str D_str until_D_E until_or_; constructor 2; auto.
intros s str B_str until_B_C H_always_until H_always; constructor 2; auto.
apply H_always_until; inversion H_always; assumption.
Qed.

Hint Resolve until_trans.

Lemma leadsto_tx_l_or :
 forall (A B C D E : stream_formula) (str : stream),
 leads_to_via A B C str ->
 leads_to_via C D E str ->
 leads_to_via (fun str : stream => A str \/ C str)
   (fun str : stream => B str \/ D str) E str.

intros A B C D E; cofix leadsto_tx_l_or.
intro str; case str; clear str.
intros s str H1 H2; constructor.
intro H; elim H; clear H.
inversion H1; eauto.
inversion H2; eauto.
unfold leads_to_via in leadsto_tx_l_or; unfold implies in leadsto_tx_l_or;
 apply leadsto_tx_l_or.
inversion H1; assumption.
inversion H2; assumption.
Qed.

Lemma until_implies_until :
 forall A B C : stream_formula,
 (forall str : stream, A str -> B str) ->
 (forall str : stream, B str -> A str) ->
 forall str : stream, B str -> (A str -> until A C str) -> until B C str.

intros A B C H_A_B H_B_A str H_B H_A_C.
cut (A str).
2: apply H_B_A; assumption.
intro H_A.
elim H_A_C; auto.
clear H_A H_B H_A_C str; intros str H_C; constructor 1; assumption.
clear H_A H_B H_A_C str; intros s str H_A H_A_C H_B_C.
constructor 2; auto.
Qed.

Hint Resolve until_implies_until.

Lemma ltv_equiv_ltv :
 forall A B C : stream_formula,
 (forall str : stream, A str -> B str) ->
 (forall str : stream, B str -> A str) ->
 forall str : stream, leads_to_via A A C str -> leads_to_via B B C str.

unfold leads_to_via in |- *; unfold implies in |- *; intros A B C H_A_B H_B_A;
 cofix ltv_equiv_ltv.
intro str; case str; clear str.
intros s str ltv_AAC; constructor;
 [ clear ltv_equiv_ltv; intro H_B; inversion ltv_AAC; eauto
 | inversion ltv_AAC; apply ltv_equiv_ltv; auto ].
Qed.

Hint Resolve ltv_equiv_ltv.

Lemma once_equiv_once :
 forall A B C : stream_formula,
 (forall str : stream, A str -> B str) ->
 (forall str : stream, B str -> A str) ->
 forall str : stream, once_until A C str -> once_until B C str.

unfold once_until in |- *; intros A B C H_A_B H_B_A str H_once; eauto.
Qed.

Lemma inv_clos :
 forall P : state_formula,
 invariant P -> forall s t : state, none_or_one_step s t -> P s -> P t.

simple induction 2; auto.
clear H0 t; intros t Hstep Ps; apply H with (s := s); assumption.
Qed.

Lemma induct :
 forall P : state_formula,
 invariant P ->
 forall str : stream,
 trace str -> P (head_str str) -> always (state2stream_formula P) str.

intros P Inv; unfold state2stream_formula in |- *; cofix induct; intro str; case str;
 simpl in |- *.
intros h tl Htrace Hhead; constructor; try assumption.
apply induct; clear induct.
inversion Htrace; assumption.
generalize Htrace; case tl; simpl in |- *.
clear Htrace tl; intros h' tl Htrace; inversion_clear Htrace;
 apply inv_clos with (s := h); assumption.
Qed.

Lemma always_P :
 forall P : stream_formula,
 (forall str : stream, trace str -> P str) ->
 forall str : stream, trace str -> always P str.

cofix always_P.
intros P H_P str; case str.
intros s tl trace_; constructor.
apply H_P; assumption.
apply always_P; auto.
inversion trace_; auto.
Qed.


Lemma safety :
 forall P : state_formula,
 (forall s : state, init_state s -> P s) ->
 invariant P -> safe (state2stream_formula P).

intros P H Inv; unfold safe in |- *; intros T Hrun; unfold run in Hrun;
 elim Hrun; clear Hrun; intros H1 H2.
apply induct; auto.
Qed.

Lemma always_implies_always :
 forall (P Q : state_formula) (str : stream),
 always (state2stream_formula P) str ->
 implies (state2stream_formula P) (state2stream_formula Q) str ->
 always (state2stream_formula Q) str.

cofix always_implies_always.
intros P Q str; case str.
intros s tl alw_P imp_P_Q; constructor.
unfold implies in imp_P_Q; inversion imp_P_Q; apply H1; inversion alw_P;
 assumption.
apply always_implies_always with (P := P); inversion alw_P.
assumption.
unfold implies in |- *; inversion imp_P_Q; assumption.
Qed.

Lemma safeP_safeQ :
 forall P Q : state_formula,
 safe (state2stream_formula P) ->
 (forall str : stream,
  implies (state2stream_formula P) (state2stream_formula Q) str) ->
 safe (state2stream_formula Q).

unfold safe in |- *.
intros P Q H_P imp_P_Q str' run_str'.
cut (implies (state2stream_formula P) (state2stream_formula Q) str'); auto.
intro imp_P_Q_str'.
apply always_implies_always with (P := P); auto.
Qed.

Lemma always_implies_always_stream :
 forall (P Q : stream_formula) (str : stream),
 always P str -> implies P Q str -> always Q str.

cofix always_implies_always_stream.
intros P Q str; case str.
intros s tl alw_P imp_P_Q; constructor.
unfold implies in imp_P_Q; inversion imp_P_Q; apply H1; inversion alw_P;
 assumption.
apply always_implies_always_stream with (P := P); inversion alw_P.
assumption.
unfold implies in |- *; inversion imp_P_Q; assumption.
Qed.

Lemma safeP_safeQ_stream :
 forall P Q : stream_formula,
 safe P -> (forall str : stream, implies P Q str) -> safe Q.

unfold safe in |- *.
intros P Q H_P imp_P_Q str' run_str'.
cut (implies P Q str'); auto.
intro imp_P_Q_str'.
apply always_implies_always_stream with (P := P); auto.
Qed.


Lemma always_always :
 forall P Q : stream_formula,
 (forall str : stream, always Q str -> P str) ->
 forall str : stream, always Q str -> always P str.

intros P Q; cofix always_always.
intros H_Q_P str; case str.
intros s tl always_Q; constructor.
apply H_Q_P; assumption.
apply always_always; auto.
inversion always_Q; assumption.
Qed.

Hint Resolve always_always.

Lemma always_always_bis :
 forall (Q : stream_formula) (str : stream),
 always Q str -> always (always Q) str.

intros Q str always_Q; eauto.
Qed.

Hint Resolve always_always_bis.

Lemma always_trace : forall str : stream, trace str -> always trace str.

unfold trace in |- *; eauto.
Qed.

Lemma always_fairstr : forall str : stream, fairstr str -> always fairstr str.

unfold fairstr in |- *; unfold infinitely_often in |- *; eauto.
Qed.

Lemma always_imp_always :
 forall (P Q : stream_formula) (str : stream),
 always P str -> (forall str : stream, P str -> Q str) -> always Q str.

intros P Q; cofix always_imp_always.
intro str; case str.
intros s tl always_P_ H_P_Q; constructor.
apply H_P_Q; inversion always_P_; assumption.
apply always_imp_always; auto.
inversion always_P_; assumption.
Qed.


Lemma always_always_implies_always :
 forall (P Q R : stream_formula) (str : stream),
 always P str ->
 always Q str ->
 (forall str : stream, P str -> Q str -> R str) -> always R str.

intros P Q R; cofix always_always_implies_always.
intro str; case str.
intros s tl always_P_ always_Q H_P_Q_R; constructor.
apply H_P_Q_R.
inversion always_P_; assumption.
inversion always_Q; assumption.
apply always_always_implies_always; auto.
inversion always_P_; assumption.
inversion always_Q; assumption.
Qed.

Lemma always_implies_always_state :
 forall (P Q R : state_formula) (str : stream),
 always (state2stream_formula P) str ->
 always (state2stream_formula Q) str ->
 (forall s : state, P s -> Q s -> R s) -> always (state2stream_formula R) str.

intros P Q R; cofix always_implies_always_state.
intro str; case str.
intros s tl always_P_ always_Q H_P_Q_R; constructor.
unfold state2stream_formula in |- *; simpl in |- *; apply H_P_Q_R.
inversion always_P_; assumption.
inversion always_Q; assumption.
apply always_implies_always_state; auto.
inversion always_P_; assumption.
inversion always_Q; assumption.
Qed.


Lemma and_always :
 forall (P Q : stream_formula) (str : stream),
 always P str -> always Q str -> always (and P Q) str.

intros P Q str always_P_ always_Q;
 apply always_always_implies_always with (P := P) (Q := Q); 
 try assumption.
unfold and in |- *; intros str' P_str' Q_str'; split; assumption.
Qed.

Lemma always_and :
 forall (P Q : stream_formula) (str : stream),
 always (and P Q) str -> always P str.

intros P Q; cofix always_and; intro str; case str.
intros s tl always_P_Q.
constructor.
inversion always_P_Q.
elim H1; auto.
apply always_and; inversion always_P_Q; assumption.
Qed.

Hint Resolve always_and.

Lemma and_always_state :
 forall (P Q : state_formula) (str : stream),
 always (state2stream_formula (and_state P Q)) str ->
 always (state2stream_formula P) str.

intros P Q; cofix and_always_state; intro str; case str.
intros s tl always_P_Q.
constructor.
unfold state2stream_formula in |- *; simpl in |- *; inversion always_P_Q.
elim H1; auto.
apply and_always_state; inversion always_P_Q; assumption.
Qed.

Hint Resolve and_always_state.

Lemma always_and_bis :
 forall (P Q : stream_formula) (str : stream),
 always (and P Q) str -> always Q str.

intros P Q; cofix always_and_bis; intro str; case str.
intros s tl always_P_Q.
constructor.
inversion always_P_Q.
elim H1; auto.
apply always_and_bis; inversion always_P_Q; assumption.
Qed.

Lemma safe_and : forall P Q : stream_formula, safe (and P Q) -> safe P.

unfold safe in |- *; intros P Q H_P_Q str H_run; cut (always (and P Q) str);
 eauto.
Qed.

Lemma safe_and_state :
 forall P Q : state_formula,
 safe (state2stream_formula (and_state P Q)) -> safe (state2stream_formula P).

unfold safe in |- *; intros P Q H_P_Q str H_run;
 cut (always (state2stream_formula (and_state P Q)) str); 
 eauto.
Qed.

Lemma always_and_and :
 forall (P Q R : stream_formula) (str : stream),
 always (and P (and Q R)) str -> always R str.

intros P Q R; cofix always_and_and; intro str; case str.
intros s tl always_P_Q_R; constructor.
inversion always_P_Q_R.
elim H1; clear H1.
intros P_str H_Q_R; elim H_Q_R; clear H_Q_R; auto.
apply always_and_and.
inversion always_P_Q_R; assumption.
Qed.

Lemma always_unless :
 forall P Q : stream_formula,
 (forall str : stream, P str -> trace str -> unless P Q str) ->
 forall str : stream,
 trace str -> always (fun str : stream => P str -> unless P Q str) str.

intros P Q unless_P_Q; cofix always_unless.
intro str; case str.
intros s tl H_trace; constructor.
intro P_str; apply unless_P_Q; assumption.
apply always_unless.
inversion H_trace; assumption.
Qed.

Lemma strong_fairstr_implies_fairstr :
 forall str : stream, strong_fairstr str -> fairstr str.

unfold fairstr in |- *; unfold strong_fairstr in |- *;
 unfold infinitely_often in |- *; intros str H_fairstr.
apply
 always_imp_always
  with
    (P := Eventually
            (fun str' : stream =>
             fair_step (head_str str') (head_str (tl_str str')))); 
 auto.
clear H_fairstr str; intros str H_ev;
 apply
  eventually_implies_eventually
   with
     (P := fun str' : stream =>
           fair_step (head_str str') (head_str (tl_str str'))); 
 auto.
Qed.

Lemma followed_until :
 forall P : stream_formula,
 (forall str : stream, P str \/ ~ P str) ->
 forall str : stream,
 is_followed P (fun str : stream => ~ P str) str ->
 until P (fun str : stream => ~ P str) str.

intros P dec str H_followed; elim (dec str).
intro P_str; unfold is_followed in H_followed.
generalize P_str; generalize H_followed; simple induction 1; try assumption.
intros str' not_P_str' P_str'; absurd (P str'); assumption.
intros s str' ev_P_str' H_P_until P_str'.
constructor 2; try assumption.
elim (dec str'); intro Pstr'.
apply H_P_until; assumption.
constructor 1; assumption.
constructor 1; assumption.
Qed.

Lemma until_eventually :
 forall (P : stream_formula) (str : stream),
 until (fun str : stream => ~ P str) P str -> Eventually P str.

intros P str H_until; elim H_until; clear H_until str.
intros str H_P; constructor 1; assumption.
intros s str H_P H_until H_ev; constructor 2; assumption.
Qed.

Lemma eventually_until :
 forall (P : stream_formula) (str : stream),
 (forall str : stream, P str \/ ~ P str) ->
 Eventually P str -> until (fun str : stream => ~ P str) P str.

intros P str dec; simple induction 1; clear H str.
intros str H_P; constructor 1; assumption.
intros s str H_ev H_until.
elim (dec (cons_str s str)); intro H_P.
constructor 1; assumption.
constructor 2; assumption.
Qed.

End LTL.

Hint Resolve always_trace.
Hint Resolve always_fairstr.



