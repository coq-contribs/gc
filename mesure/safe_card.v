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
(*                               safe_card.v                                *)
(****************************************************************************)

Section safe_card.

Require Export white_card.
Require Export black_card.
Require Export grey_card.
Require Export mesure.
Require Export safety.

Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Safe :=
  (safe init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Invariant :=
  (invariant (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Stream := (stream state) (only parsing).
Notation Run :=
  (run init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation State_formula := (state_formula state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).

Lemma step_black_card :
 forall s t : state,
 (exists b : nat, card_color black (mk s) b) ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 exists b : nat, card_color black (mk t) b. 

unfold invariant in |- *; unfold leads_to in |- *.
intros s t H_s step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve step_black_card.

Lemma inv_black_card :
 invariant (fun (a : label) (s t : state) => transition s t a)
   (fun s : state => exists b : nat, card_color black (mk s) b).

unfold invariant in |- *; unfold leads_to in |- *; eauto.
Qed.

Hint Resolve inv_black_card.

Lemma safe_card_black :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula
      (fun s : state => exists b : nat, card_color black (mk s) b)).

apply safety; eauto.
Qed.

Hint Resolve safe_card_black.

Lemma always_card_black :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula
      (fun s : state => exists b : nat, card_color black (mk s) b)) str.

intros str H_run.
cut
 (safe init_state (fun (a : label) (s t : state) => transition s t a)
    (state2stream_formula
       (fun s : state => exists b : nat, card_color black (mk s) b))); 
 eauto.
Qed.
                                              
Hint Resolve always_card_black.

Lemma step_white_card :
 forall s t : state,
 rt_grey_or_black s ->
 (exists b : nat, card_color black (mk s) b) ->
 (exists w : nat, card_color white (mk s) w) ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 exists w : nat, card_color white (mk t) w. 

unfold invariant in |- *; unfold leads_to in |- *.
intros s t safety_prop cardb_s cardw_s step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve step_white_card.

Definition conj_inv : state_formula state :=
  fun s =>
  (exists w : nat, card_color white (mk s) w) /\
  (exists b : nat, card_color black (mk s) b) /\ rt_grey_or_black s.

Lemma init_conj_inv : forall s : state, init_state s -> conj_inv s.

intros s init; unfold conj_inv in |- *; split; eauto.
Qed.

Hint Resolve init_conj_inv.

Lemma invariant_conj_inv :
 invariant (fun (a : label) (s t : state) => transition s t a) conj_inv.

unfold invariant in |- *; unfold leads_to in |- *; unfold conj_inv in |- *.
intros s t inv step; elim inv; clear inv.
intros cardw_s inv; elim inv; clear inv.
intros cardb_s H_rt_s; split; eauto.
Qed.

Hint Resolve invariant_conj_inv.

Lemma safe_conj_inv :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula conj_inv).

apply safety; eauto.
Qed.

Hint Resolve safe_conj_inv.

Lemma safe_card_white :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula
      (fun s : state => exists b : nat, card_color white (mk s) b)).

apply
 safe_and_state
  with
    (Q := and_state
            (fun s : state => exists b : nat, card_color black (mk s) b)
            rt_grey_or_black); eauto.
Qed.

Hint Resolve safe_card_white.

Lemma always_card_white :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula
      (fun s : state => exists w : nat, card_color white (mk s) w)) str.

intros str H_run.
cut
 (safe init_state (fun (a : label) (s t : state) => transition s t a)
    (state2stream_formula
       (fun s : state => exists w : nat, card_color white (mk s) w))); 
 eauto.
Qed.
                                              
Hint Resolve always_card_white.

Lemma step_grey_card :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 (exists b : nat, card_color grey (mk s) b) ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 exists b : nat, card_color grey (mk t) b. 

unfold invariant in |- *; unfold leads_to in |- *.
intros s t cardw_s cardg_s step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve step_grey_card.

Definition inv_conj : state_formula state :=
  fun s =>
  (exists g : nat, card_color grey (mk s) g) /\
  rt_grey_or_black s /\
  (exists b : nat, card_color black (mk s) b) /\
  (exists w : nat, card_color white (mk s) w).

Lemma init_inv_conj : forall s : state, init_state s -> inv_conj s.

intros s init; unfold inv_conj in |- *; split; eauto.
Qed.

Hint Resolve init_inv_conj.

Lemma invariant_inv_conj :
 invariant (fun (a : label) (s t : state) => transition s t a) inv_conj.

unfold invariant in |- *; unfold leads_to in |- *; unfold inv_conj in |- *.
intros s t inv step; elim inv; clear inv.
intros cardg_s inv; elim inv; clear inv.
intros H_rt inv; elim inv; clear inv.
intros cardb_s cardw_s; split; eauto.
split; eauto.
Qed.

Hint Resolve invariant_inv_conj.

Lemma safe_inv_conj :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula inv_conj).

apply safety; eauto.
Qed.

Hint Resolve safe_inv_conj.

Lemma safe_card_grey :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula
      (fun s : state => exists g : nat, card_color grey (mk s) g)).

apply
 safe_and_state
  with
    (Q := and_state rt_grey_or_black
            (and_state
               (fun s : state => exists b : nat, card_color black (mk s) b)
               (fun s : state => exists w : nat, card_color white (mk s) w)));
 eauto.
Qed.

Hint Resolve safe_card_grey.

Lemma always_card_grey :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula
      (fun s : state => exists g : nat, card_color grey (mk s) g)) str.

intros str H_run.
cut
 (safe init_state (fun (a : label) (s t : state) => transition s t a)
    (state2stream_formula
       (fun s : state => exists g : nat, card_color grey (mk s) g))); 
 eauto.
Qed.
                                              
Hint Resolve always_card_grey.

Definition g_w_b : stream_formula state :=
  and
    (state2stream_formula
       (fun s : state => exists g : nat, card_color grey (mk s) g))
    (and
       (state2stream_formula
          (fun s : state => exists b : nat, card_color black (mk s) b))
       (state2stream_formula
          (fun s : state => exists w : nat, card_color white (mk s) w))).

Lemma always_gwb :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always g_w_b str.

intros str H_run; unfold g_w_b in |- *.
apply and_always; eauto.
apply and_always; eauto.
Qed.

Hint Resolve always_gwb.

Lemma safe_gwb :
 safe init_state (fun (a : label) (s t : state) => transition s t a) g_w_b.

unfold safe in |- *; eauto.
Qed.

Lemma step_mesure :
 forall (s t : state) (nb : nat),
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 mesure (mk s) 0 \/
 (nb <> 0 /\ mesure (mk s) nb -> mesure (mk t) nb \/ mesure (mk t) (pred nb)).

intros s t nb step; elim step; clear step.
intro a; case a; intro trans; inversion trans.
right; intro H_mes; elim H_mes; clear H_mes; intros H_nb mes_s; left; eauto.
right; intro H_mes; elim H_mes; clear H_mes; intros H_nb mes_s; left; eauto.
right; intro H_mes; elim H_mes; clear H_mes; intros H_nb mes_s; left; eauto.
cut
 (mesure (mk s) 0 \/ (mesure (mk s) nb -> nb <> 0 /\ mesure (mk t) (pred nb)));
 eauto.
intro H_mes; elim H_mes; clear H_mes; auto.
intro H_mes; right; right.
elim H_mes; auto.
elim H0; auto.
right; intro H_mes; elim H_mes; clear H_mes.
intros H_nb mes_s; right; eauto.
right; intro H_mes; elim H_mes; clear H_mes; intros H_nb mes_s; left; eauto.
right; intro H_mes; elim H_mes; clear H_mes.
intros H_nb mes_s; right; eauto.
right; intro H_mes; elim H_mes; clear H_mes.
intros H_nb mes_s; right; eauto.
right; intro H_mes; elim H_mes; clear H_mes; intros H_nb mes_s; left; eauto.
Qed.

Hint Immediate gccall_ex_mesure.

Lemma step_ex_mesure :
 forall s t : state,
 rt_grey_or_black s ->
 (exists b : nat, card_color black (mk s) b) ->
 (exists nb : nat, mesure (mk s) nb) ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 exists nb : nat, mesure (mk t) nb.

intros s t H_rt card_s H_mes step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve step_ex_mesure.

Definition inv_conj_mes : state_formula state :=
  fun s =>
  (exists nb : nat, mesure (mk s) nb) /\
  rt_grey_or_black s /\ (exists b : nat, card_color black (mk s) b).

Lemma init_inv_conj_mes : forall s : state, init_state s -> inv_conj_mes s.

intros s init; unfold inv_conj in |- *; split; eauto.
Qed.

Hint Resolve init_inv_conj_mes.

Lemma invariant_inv_conj_mes :
 invariant (fun (a : label) (s t : state) => transition s t a) inv_conj_mes.

unfold invariant in |- *; unfold leads_to in |- *;
 unfold inv_conj_mes in |- *.
intros s t inv step; elim inv; clear inv.
intros H_mes inv; elim inv; clear inv.
intros H_rt cardb_s; split; eauto.
Qed.

Hint Resolve invariant_inv_conj_mes.

Lemma safe_inv_conj_mes :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula inv_conj_mes).

apply safety; eauto.
Qed.

Hint Resolve safe_inv_conj_mes.

Lemma safe_mesure :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb)).

apply
 safe_and_state
  with
    (Q := and_state rt_grey_or_black
            (fun s : state => exists b : nat, card_color black (mk s) b));
 eauto.
Qed.

Hint Resolve safe_mesure.

Lemma always_mesure :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb))
   str.

intros str H_run.
cut
 (safe init_state (fun (a : label) (s t : state) => transition s t a)
    (state2stream_formula
       (fun s : state => exists nb : nat, mesure (mk s) nb))); 
 eauto.
Qed.
                                              
Hint Resolve always_mesure.

End safe_card.

Hint Resolve always_gwb.
Hint Resolve safe_gwb.
Hint Resolve step_mesure.
Hint Resolve always_mesure.
Hint Resolve always_mesure.