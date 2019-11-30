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
(*                               safety.v                                   *)
(****************************************************************************)

Section safety.

Require Export rtgreyorblack.
Require Export noedgeblacktowhite.
Require Export accnotfree.
Require Export nogreyaccnblackn.
Require Export sweepnogrey.

Notation State_formula := (state_formula state) (only parsing).
Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Safe :=
  (safe init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Invariant :=
  (invariant (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Run :=
  (run init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Stream := (stream state) (only parsing).

Hint Immediate rt_grey_or_black_init.
Hint Immediate no_edge_black_to_white_init.
Hint Immediate acc_imp_notfree_init.
Hint Immediate nogrey_accn_imp_blackn_init.
Hint Immediate sweep_no_greys_init.

Lemma rt_grey_or_black_step :
 forall s t : state,
 rt_grey_or_black s ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 rt_grey_or_black t.

intros s t H_rt step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve rt_grey_or_black_step.

Lemma rt_grey_or_black_inv :
 invariant (fun (a : label) (s t : state) => transition s t a)
   rt_grey_or_black.

unfold invariant in |- *; unfold leads_to in |- *; eauto.
Qed.

Lemma sweep_no_greys_step :
 forall s t : state,
 sweep_no_greys s ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 sweep_no_greys t.

intros s t H_sweep step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve sweep_no_greys_step.

Lemma sweep_no_greys_inv :
 invariant (fun (a : label) (s t : state) => transition s t a) sweep_no_greys.

unfold invariant in |- *; unfold leads_to in |- *; eauto.
Qed.

Hint Resolve sweep_no_greys_inv.

Lemma safe_sweep_no_greys :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula (fun s : state => sweep_no_greys s)).

apply safety; eauto.
Qed.

Hint Resolve safe_sweep_no_greys.

Lemma always_sweep_no_grey :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str.

eauto.
Qed.

Lemma no_edge_black_to_white_step :
 forall s t : state,
 no_edge_black_to_white s ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 no_edge_black_to_white t.

intros s t H_edge step.
elim step; intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Hint Resolve no_edge_black_to_white_step.

Lemma no_edge_black_to_white_inv :
 invariant (fun (a : label) (s t : state) => transition s t a)
   no_edge_black_to_white.

unfold invariant in |- *; unfold leads_to in |- *; eauto.
Qed.

Lemma acc_imp_notfree_step :
 forall s t : state,
 acc_imp_notfree s ->
 nogrey_accn_imp_blackn s ->
 sweep_no_greys s ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 acc_imp_notfree t.
                      
intros s t H_s inv5_s inv4_s step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
Qed.

Lemma nogrey_accn_imp_blackn_step :
 forall s t : state,
 rt_grey_or_black s ->
 no_edge_black_to_white s ->
 acc_imp_notfree s ->
 nogrey_accn_imp_blackn s ->
 sweep_no_greys s ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 nogrey_accn_imp_blackn t.
                      
intros s t inv1_s inv2_s H_s inv5_s inv4_s step.
elim step.
intro a; case a; intro trans; inversion_clear trans; eauto.
apply (nogrey_accn_imp_blackn_gccall s t); auto.
apply (nogrey_accn_imp_blackn_marknode s t); auto.
Qed.

Hint Resolve rt_grey_or_black_inv.
Hint Resolve no_edge_black_to_white_inv.
Hint Resolve acc_imp_notfree_step.
Hint Resolve nogrey_accn_imp_blackn_step.
Hint Resolve sweep_no_greys_inv.

Definition invariant_safety : state_formula state :=
  fun s =>
  rt_grey_or_black s /\
  no_edge_black_to_white s /\
  acc_imp_notfree s /\ nogrey_accn_imp_blackn s /\ sweep_no_greys s.

Lemma init_invariant_safe :
 forall s : state, init_state s -> invariant_safety s.

intros s init; split; eauto.
Qed.

Hint Resolve init_invariant_safe.

Lemma inv_invariant_safety :
 invariant (fun (a : label) (s t : state) => transition s t a)
   invariant_safety.

unfold invariant in |- *; unfold leads_to in |- *;
 unfold invariant_safety in |- *.
intros s t inv_s trans; elim inv_s; clear inv_s.
intros inv1_s inv_s; elim inv_s; clear inv_s.
intros inv2_s inv_s; elim inv_s; clear inv_s.
intros inv3_s inv_s; elim inv_s; clear inv_s.
intros inv4_s inv5_s; split; eauto.
split; eauto.
split; eauto.
Qed.

Hint Resolve inv_invariant_safety.

Lemma invariant_safe :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula invariant_safety).

apply safety; eauto.
Qed.

Hint Resolve invariant_safe.

Lemma always_inv_safety :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always (state2stream_formula invariant_safety) str.

eauto.
Qed.

Hint Resolve always_inv_safety.

Notation Stream_formula := (stream_formula state) (only parsing).

Definition invariant_safety_and : stream_formula state :=
  and (state2stream_formula (fun s : state => rt_grey_or_black s))
    (and (state2stream_formula (fun s : state => no_edge_black_to_white s))
       (and (state2stream_formula (fun s : state => acc_imp_notfree s))
          (and
             (state2stream_formula
                (fun s : state => nogrey_accn_imp_blackn s))
             (state2stream_formula (fun s : state => sweep_no_greys s))))).

Lemma always_invariant_safety_and :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always invariant_safety_and str.

unfold invariant_safety_and in |- *; unfold and in |- *; eauto.
Qed.

Hint Resolve always_invariant_safety_and.

Lemma always_nogrey_accn_imp_blackn :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str.

intros str H_run; cut (always invariant_safety_and str); eauto.
unfold invariant_safety_and in |- *; intro H_always.
cut
 (always
    (and (state2stream_formula (fun s : state => acc_imp_notfree s))
       (and
          (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
          (state2stream_formula (fun s : state => sweep_no_greys s)))) str).
2: apply
    always_and_and
     with
       (P := state2stream_formula (fun s : state => rt_grey_or_black s))
       (Q := state2stream_formula (fun s : state => no_edge_black_to_white s));
    assumption.
clear H_always; intro H_always.
cut
 (always
    (and (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
       (state2stream_formula (fun s : state => sweep_no_greys s))) str).
2: apply
    always_and_bis
     with (P := state2stream_formula (fun s : state => acc_imp_notfree s));
    assumption.
clear H_always; intro H_always.
apply
 always_and
  with (Q := state2stream_formula (fun s : state => sweep_no_greys s));
 assumption.
Qed.

Definition safety_prop : state_formula state :=
  fun s => forall n : node, mk s n = free -> ~ accessible node (hp s) rt n.

Lemma inv_safety_prop : forall s : state, invariant_safety s -> safety_prop s.
    
unfold invariant_safety in |- *; unfold acc_imp_notfree in |- *;
 unfold safety_prop in |- *; intros s inv_s n mksn.
elim inv_s; clear inv_s.
intros inv1_s inv_s; elim inv_s; clear inv_s.
intros inv2_s inv_s; elim inv_s; clear inv_s.
intros inv3_s inv_s; intro acces_n_s.
unfold not in inv3_s; apply inv3_s with (n := n); assumption.
Qed.

Hint Resolve inv_safety_prop.

Lemma implies_safety_prop :
 forall str : stream state,
 implies (state2stream_formula invariant_safety)
   (state2stream_formula safety_prop) str.

unfold implies in |- *.
cofix implies_safety_prop.
intro str; case str.
intros s tl; constructor; auto.
unfold state2stream_formula in |- *; simpl in |- *; eauto.
Qed.

Hint Resolve implies_safety_prop.

Lemma safety_prop_safe :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (state2stream_formula safety_prop).

apply safeP_safeQ with (P := invariant_safety); eauto.
Qed.

End safety.

Hint Resolve rt_grey_or_black_step.
Hint Resolve safe_sweep_no_greys.
Hint Resolve always_sweep_no_grey.
Hint Resolve always_nogrey_accn_imp_blackn.
