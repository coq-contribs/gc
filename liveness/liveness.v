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
(*                               liveness.v                                 *)
(****************************************************************************)

Section liveness.

Require Export card_facts.
Require Export parameters_card.
Require Export safe_card.
Require Export fairstr.
Require Export notacc_white_nogrey.
Require Export notacc_black_nogrey.
Require Export notacc_init.
Require Export notacc_white_ancestor.
Require Export until_zero.
Require Export LTL.

Notation Trace := (trace (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Stream := (stream state) (only parsing).
Notation Strong_fairstr :=
  (strong_fairstr (fun (a : label) (s t : state) => transition s t a) fair)
  (only parsing).
Notation Run :=
  (run init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Safe :=
  (safe init_state (fun (a : label) (s t : state) => transition s t a))
  (only parsing).

Definition and_inv : stream_formula state :=
  and (state2stream_formula (fun s : state => sweep_no_greys s))
    (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s)).

Lemma safe_inv_and_gwb :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (and and_inv g_w_b).

unfold safe in |- *; intros str H_run.
apply and_always; eauto.
unfold and_inv in |- *; apply and_always; eauto.
Qed.

Hint Resolve safe_inv_and_gwb.

Lemma safe_inv_gwb_mesure :
 safe init_state (fun (a : label) (s t : state) => transition s t a)
   (and (and and_inv g_w_b)
      (state2stream_formula
         (fun s : state => exists nb : nat, mesure (mk s) nb))).

unfold safe in |- *; intros str H_run.
apply and_always; eauto.
Qed.

Hint Resolve safe_inv_gwb_mesure.

Lemma always_and_inv_g_w_b :
 forall str : stream state,
 always
   (and (and and_inv g_w_b)
      (state2stream_formula
         (fun s : state => exists nb : nat, mesure (mk s) nb))) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str /\
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str /\
 always
   (state2stream_formula
      (fun s : state => exists w : nat, card_color white (mk s) w)) str /\
 always
   (state2stream_formula
      (fun s : state => exists g : nat, card_color grey (mk s) g)) str /\
 always
   (state2stream_formula (fun s : state => exists nb : nat, mesure (mk s) nb))
   str.

unfold and_inv in |- *; unfold g_w_b in |- *;
 intros str H_always_inv_gwb_mesure.
cut
 (always
    (and
       (and (state2stream_formula (fun s : state => sweep_no_greys s))
          (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s)))
       (and
          (state2stream_formula
             (fun s : state => exists g : nat, card_color grey (mk s) g))
          (and
             (state2stream_formula
                (fun s : state => exists b : nat, card_color black (mk s) b))
             (state2stream_formula
                (fun s : state => exists w : nat, card_color white (mk s) w)))))
    str).    
intro H_always; split.
cut
 (always
    (and (state2stream_formula (fun s : state => sweep_no_greys s))
       (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s)))
    str).
intro H_always_inv.
apply
 always_and
  with
    (Q := state2stream_formula (fun s : state => nogrey_accn_imp_blackn s));
 assumption.
apply
 always_and
  with
    (Q := and
            (state2stream_formula
               (fun s : state => exists g : nat, card_color grey (mk s) g))
            (and
               (state2stream_formula
                  (fun s : state => exists b : nat, card_color black (mk s) b))
               (state2stream_formula
                  (fun s : state => exists w : nat, card_color white (mk s) w))));
 assumption.
split.
cut
 (always
    (and (state2stream_formula (fun s : state => sweep_no_greys s))
       (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s)))
    str).
intro H_always_inv.
apply
 always_and_bis
  with (P := state2stream_formula (fun s : state => sweep_no_greys s));
 assumption.
apply
 always_and
  with
    (Q := and
            (state2stream_formula
               (fun s : state => exists g : nat, card_color grey (mk s) g))
            (and
               (state2stream_formula
                  (fun s : state => exists b : nat, card_color black (mk s) b))
               (state2stream_formula
                  (fun s : state => exists w : nat, card_color white (mk s) w))));
 assumption.
split;
 cut
  (always
     (and
        (state2stream_formula
           (fun s : state => exists g : nat, card_color grey (mk s) g))
        (and
           (state2stream_formula
              (fun s : state => exists b : nat, card_color black (mk s) b))
           (state2stream_formula
              (fun s : state => exists w : nat, card_color white (mk s) w))))
     str).
intro H_always_gwb.
cut
 (always
    (and
       (state2stream_formula
          (fun s : state => exists b : nat, card_color black (mk s) b))
       (state2stream_formula
          (fun s : state => exists w : nat, card_color white (mk s) w))) str).
intro H_always_and.
apply
 always_and_bis
  with
    (P := state2stream_formula
            (fun s : state => exists b : nat, card_color black (mk s) b));
 assumption.
apply
 always_and_bis
  with
    (P := state2stream_formula
            (fun s : state => exists g : nat, card_color grey (mk s) g));
 assumption.
apply
 always_and_bis
  with
    (P := and (state2stream_formula (fun s : state => sweep_no_greys s))
            (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s)));
 assumption.
intro H_always_and.
split.
apply
 always_and
  with
    (Q := and
            (state2stream_formula
               (fun s : state => exists b : nat, card_color black (mk s) b))
            (state2stream_formula
               (fun s : state => exists w : nat, card_color white (mk s) w)));
 assumption.
apply
 always_and_bis
  with
    (P := and
            (and (state2stream_formula (fun s : state => sweep_no_greys s))
               (state2stream_formula
                  (fun s : state => nogrey_accn_imp_blackn s)))
            (and
               (state2stream_formula
                  (fun s : state => exists g : nat, card_color grey (mk s) g))
               (and
                  (state2stream_formula
                     (fun s : state =>
                      exists b : nat, card_color black (mk s) b))
                  (state2stream_formula
                     (fun s : state =>
                      exists w : nat, card_color white (mk s) w)))));
 assumption.
apply
 always_and_bis
  with
    (P := and (state2stream_formula (fun s : state => sweep_no_greys s))
            (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s)));
 assumption.
apply
 always_and
  with
    (Q := state2stream_formula
            (fun s : state => exists nb : nat, mesure (mk s) nb)); 
 assumption.
Qed.

Hint Resolve always_and_inv_g_w_b.

Lemma run_fairstr_always :
 forall P : stream_formula state,
 (forall str : stream state,
  trace (fun (a : label) (s t : state) => transition s t a) str ->
  strong_fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
  always
    (and (and and_inv g_w_b)
       (state2stream_formula
          (fun s : state => exists nb : nat, mesure (mk s) nb))) str -> 
  P str) ->
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 strong_fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 always P str.

unfold strong_fairstr in |- *; unfold infinitely_often in |- *; intros P H.
intros str H_run H_always.
apply
 always_on_run
  with
    (label := label)
    (init_state := init_state)
    (transition := fun (a : label) (s t : state) => transition s t a)
    (F := Eventually
            (fun str' : stream state =>
             fair_step (fun (a : label) (s t : state) => transition s t a)
               fair (head_str str') (head_str (tl_str str'))))
    (I := and (and and_inv g_w_b)
            (state2stream_formula
               (fun s : state => exists nb : nat, mesure (mk s) nb))); 
 eauto.
Qed.

Lemma card_grey_rt :
 forall s : state,
 (forall n : node, n <> rt -> mk s n = white \/ mk s n = free) ->
 mk s rt = grey -> card_color grey (mk s) 1.

intros s H_col mksrt; elim (exist_updated node color black (mk s) rt).
intros mk' mark; elim mark; clear mark.
intros mark' mk'rt.
unfold card_color in |- *; apply card_S with (M1 := mk') (a0 := rt); auto.
constructor; intro n; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; rewrite mk'rt; discriminate.
intro ndifrt; rewrite <- (mark' n ndifrt).
elim (H_col n ndifrt); intro mksn; rewrite mksn; discriminate.
symmetry  in |- *; apply mark'; auto.
rewrite mk'rt; discriminate.
Qed.

Lemma def_equiv :
 forall (n : node) (str : stream state),
 notacc_white_init_formula n str -> notacc_white_exgrey_reach_formula n str.

intros n str H; elim H; clear H.
intros notacc_n H; elim H; clear H.
intros mkhn H; elim H; clear H.
intros mkhrt H_n; split; auto.
split; auto.
split.
exists 1; split; auto.
apply card_grey_rt; auto.
intros m H_reach; apply H_n.
intro meqrt; absurd (accessible node (hp (head_str str)) rt n); auto.
replace (accessible node (hp (head_str str)) rt n) with
 (reachable node (hp (head_str str)) rt n); auto.
rewrite <- meqrt; assumption.
Qed.

Hint Resolve def_equiv.

Lemma liveness :
 forall str : stream state,
 run init_state (fun (a : label) (s t : state) => transition s t a) str ->
 strong_fairstr (fun (a : label) (s t : state) => transition s t a) fair str ->
 forall n : node,
 is_always_followed
   (state2stream_formula (fun s : state => ~ accessible node (hp s) rt n))
   (state2stream_formula (fun s : state => mk s n = free)) str.

unfold is_always_followed in |- *; intros str H_run H_fairstr n.
apply run_fairstr_always; try assumption.
clear H_run H_fairstr str; intros str H_trace H_fairstr always_inv_gwb.
unfold is_followed in |- *.
cut
 (always (state2stream_formula (fun s : state => sweep_no_greys s)) str /\
  always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
    str /\
  always
    (state2stream_formula
       (fun s : state => exists w : nat, card_color white (mk s) w)) str /\
  always
    (state2stream_formula
       (fun s : state => exists g : nat, card_color grey (mk s) g)) str /\
  always
    (state2stream_formula
       (fun s : state => exists nb : nat, mesure (mk s) nb)) str); 
 eauto.
intro H; elim H; clear H.
intros H_always_sweep H; elim H; clear H.
intros H_always_inv H; elim H; clear H.
intros H_always_white H; elim H; clear H.
intros H_always_grey H_always_mesure.
cut
 (always
    (Eventually
       (state2stream_formula (fun s : state => card_color white (mk s) 0)))
    str);
 [ intro H_alw_ev_white
 | apply always_eventually_white_until_zero_trace; auto ].
cut
 (always
    (Eventually
       (state2stream_formula (fun s : state => card_color grey (mk s) 0)))
    str);
 [ intro H_alw_ev_grey
 | apply always_eventually_grey_until_zero_trace; auto ].
2: apply strong_fairstr_implies_fairstr; assumption.
2: apply strong_fairstr_implies_fairstr; assumption.
intro notacc_n;
 cut
  (until
     (state2stream_formula (fun s : state => ~ accessible node (hp s) rt n))
     (free_or_notfree_notacc_nogrey n) str).


(*  (A n str)U(B n str)-> (D n str)*)
intro H_until.
generalize H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
clear H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace always_inv_gwb
 notacc_n.
elim H_until; clear H_until str.

(* BASE CASE 1*)

intros str H_n H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.

(*  H_n: (B n str)*)
elim H_n; clear H_n.

(* 1st case : n is free  *)

intro mkhdn; constructor 1; assumption.

(* 2nd case: n is not free, non acc, g=0 *)

intro H; elim H; clear H.
intros H H_card; elim H; clear H.
intros mkhdn notacc_n.

(* n is white or not white *)
elim (eq_dec_color (mk (head_str str) n) white); intro mkhn.

(* n is white *)
apply white_notacc_nogrey_until_eventually_free; auto.
inversion H_alw_ev_white; auto.
split; auto.

(* m is not white*)

(* (F n)U(G n) str)*)
cut
 (until (fun str => notacc_black_nogrey_formula n str)
    (fun str => notacc_black_nomeasure_formula n str) str).

intro H_until.
generalize H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
clear H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
elim H_until; clear H_until mkhn notacc_n mkhdn H_card str.


(*BASE CASE 2*)
intros str H_n H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
(* H_n:(G n str)*)

(* (G n)U(H n) *)
cut
 (until (fun str => notacc_black_nomeasure_formula n str)
    (fun str => notacc_white_init_formula n str) str).
2: apply until_no_measure_init; auto.
intro H_until.
generalize H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
clear H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
elim H_until; clear H_until H_n str.

(*BASE CASE 3*)
intros str H_n H_alw_ev_grey H_alw_ev_white H_always_mesure H_always_grey
 H_always_white H_always_inv H_always_sweep H_fairstr H_trace.

(* H_n:(H n str) *)

(* (K n s)*)
cut (notacc_white_exgrey_reach_formula n str); eauto.
intro H.
apply notacc_white_nogrey_eventually_free; auto.
inversion H_alw_ev_grey; auto.
intros s str H_n H_until H_ind H_alw_ev_grey H_alw_ev_white H_always_mesure
 H_always_grey H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
inversion H_alw_ev_grey; inversion H_alw_ev_white; inversion H_always_mesure;
 inversion H_always_grey; inversion H_always_white; 
 inversion H_always_inv; inversion H_always_sweep; 
 inversion H_fairstr; inversion H_trace.
constructor 2; apply H_ind; assumption.
intros s str H_n H_until H_ind H_alw_ev_grey H_alw_ev_white H_always_mesure
 H_always_grey H_always_white H_always_inv H_always_sweep H_fairstr H_trace;
 inversion H_alw_ev_grey; inversion H_alw_ev_white; 
 inversion H_always_mesure; inversion H_always_grey; 
 inversion H_always_white; inversion H_always_inv; 
 inversion H_always_sweep; inversion H_fairstr; inversion H_trace.
constructor 2; apply H_ind; assumption.
apply until_no_measure; auto.
inversion H_alw_ev_white; auto.
split; auto.
split; auto.
generalize (refl_equal (mk (head_str str) n));
 pattern (mk (head_str str) n) at -1 in |- *; case (mk (head_str str) n);
 intro mk_h_n; trivial.
absurd (mk (head_str str) n = white); assumption.
inversion_clear H_card; absurd (mk (head_str str) n = grey); auto.
absurd (mk (head_str str) n = free); assumption.
intros s str H_n H_until H_ind H_alw_ev_grey H_alw_ev_white H_always_mesure
 H_always_grey H_always_white H_always_inv H_always_sweep H_fairstr H_trace.
inversion H_alw_ev_grey; inversion H_alw_ev_white; inversion H_always_mesure;
 inversion H_always_grey; inversion H_always_white; 
 inversion H_always_inv; inversion H_always_sweep; 
 inversion H_fairstr; inversion H_trace.
constructor 2.
apply H_ind; assumption.
apply until_free_or_nogrey; auto.
inversion H_alw_ev_grey; auto.
Qed.

End liveness.


    