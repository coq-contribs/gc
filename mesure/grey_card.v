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
(*                               grey_card.v                                *)
(****************************************************************************)

Section grey_card.

Require Export card_facts.
Require Export parameters_card.
Require Export lemme_arith.
Require Export lemma_step.
Require Export Arith.
Require Export Peano_dec.
Require Export Bool.

Notation Card := (card _ _) (only parsing).

Lemma init_grey : forall s : state, init_state s -> card_color grey (mk s) 0.

intros s init; elim init; clear init.
intros ctls init; elim init; clear init.
intros mark heap; elim mark; clear mark.
intros mksrt mark; constructor.
intros n; elim (eq_dec_node n rt).
intros neqrt; rewrite neqrt; rewrite mksrt; discriminate.
intros ndifrt; rewrite (mark n ndifrt); discriminate.
Qed.

Hint Resolve init_grey.

Lemma ex_init_grey :
 forall s : state, init_state s -> exists g : nat, card_color grey (mk s) g.

intros s init; exists 0; eauto.
Qed.


Lemma add_grey :
 forall (s t : state) (g : nat),
 card_color grey (mk s) g ->
 add_edge s t -> card_color grey (mk t) g \/ card_color grey (mk t) (S g).

intros s t g card_s addedge; elim addedge; clear addedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark; elim mark; clear mark.
intro cas1; elim cas1; clear cas1.
intros mksn1 eqmk; left; rewrite eqmk; assumption.
intro cas; elim cas; clear cas.
intro cas2; elim cas2; clear cas2.
intros mksn1 eqmk; elim eqmk; clear eqmk.
intros mksn2 eqmk; left; rewrite eqmk; assumption.
intro cas3; elim cas3; clear cas3.
intros mksn1 mk2; elim mk2; clear mk2.
intros mksn2 updcol; elim updcol; clear updcol.
intros mark mktn2; right; unfold card_color in |- *;
 apply card_S with (M1 := mk s) (a0 := n2); auto.
rewrite mksn2; discriminate.
Qed.


Lemma ex_add_grey :
 forall s t : state,
 (exists g : nat, card_color grey (mk s) g) ->
 add_edge s t -> exists g : nat, card_color grey (mk t) g.

intros s t card_s addedge; elim addedge; clear addedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark.
elim mark; clear mark.
intro cas1; elim cas1; clear cas1.
intros mksn1 eqmk; rewrite eqmk; assumption.
intro cas; elim cas; clear cas.
intro cas2; elim cas2; clear cas2.
intros mksn1 eqmk; elim eqmk; clear eqmk.
intros mksn2 eqmk; rewrite eqmk; assumption.
intro cas3; elim cas3; clear cas3.
intros mksn1 mk2; elim mk2; clear mk2.
intros mksn2 updcol; elim updcol; clear updcol.
intros mark mktn2; elim card_s; clear card_s.
intros g card_s; exists (S g).
unfold card_color in |- *.
apply card_S with (M1 := mk s) (a0 := n2); auto.
rewrite mksn2; discriminate.
Qed.


Lemma remove_grey :
 forall (s t : state) (g : nat),
 card_color grey (mk s) g -> remove_edge s t -> card_color grey (mk t) g.

intros s t g card_s removeedge.
elim removeedge; clear removeedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt remove mark.
rewrite mark; assumption.
Qed.

Hint Resolve remove_grey.

Lemma ex_remove_grey :
 forall s t : state,
 (exists g : nat, card_color grey (mk s) g) ->
 remove_edge s t -> exists g : nat, card_color grey (mk t) g.

intros s t card_s removeedge; elim card_s; clear card_s.
intros g card_s; exists g; eauto.
Qed.


Lemma alloc_grey :
 forall (s t : state) (g : nat),
 card_color grey (mk s) g -> alloc s t -> card_color grey (mk t) g.

intros s t g card_s alloc; unfold card_color in |- *;
 apply card_inv with (M1 := mk s); auto.
intros n mksn; apply (alloc_notgreys_notgreyt s t); assumption.
intros n mksn; apply (alloc_greys_greyt s t); assumption.
Qed.

Hint Resolve alloc_grey.


Lemma ex_alloc_grey :
 forall s t : state,
 (exists g : nat, card_color grey (mk s) g) ->
 alloc s t -> exists g : nat, card_color grey (mk t) g.

intros s t card_s alloc; elim card_s; clear card_s.
intros g card_s; exists g; eauto.
Qed.


Lemma initcol_grey :
 forall s t : state,
 (forall n : node, mk s n = black \/ mk s n = free) ->
 init_color (mk s) (mk t) -> card_color grey (mk t) 1.

intros s t H_col init; elim init; clear init.
intros mktrt mark; elim mark; clear mark.
intros mark1 mark2; elim (exist_updated node color (mk s rt) (mk t) rt).
intros mk' mark; elim mark; clear mark.
intros mark' mk'rt; unfold card_color in |- *;
 apply card_S with (M1 := mk') (a0 := rt); auto.
constructor; intro n; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; rewrite mk'rt.
elim (H_col rt); intro mksrt; rewrite mksrt; discriminate.
intro ndifrt; rewrite <- (mark' n ndifrt).
elim (eq_dec_color (mk s n) black); intro mksn.
rewrite (mark1 n ndifrt); auto.
discriminate.
rewrite (mark2 n ndifrt); auto.
elim (H_col n); intro mksn2; rewrite mksn2; discriminate.
symmetry  in |- *; apply mark'; auto.
rewrite mk'rt; elim (H_col rt); intro mksrt; rewrite mksrt; discriminate.
Qed.

Hint Resolve initcol_grey.

Lemma card_grey_marknode :
 forall (nb : nat) (m1 : marking) (h1 : heap) (n0 : node),
 card_sons n0 white m1 h1 nb ->
 forall (m2 : marking) (h2 : heap) (g : nat),
 card_color grey m1 g ->
 m1 n0 = grey ->
 m2 n0 <> grey ->
 grey_white_sons m1 m2 h1 h2 n0 -> card_color grey m2 (pred (g + nb)).

simple induction nb; clear nb.
intros m1 h1 n0 H_cardsons_m1 m2 h2 g H_card_m1 m1n0 m2n0 H_grey.
rewrite <- (plus_n_O g).
elim H_grey; clear H_grey.
intros heap H_col1 H_col2; unfold card_color in |- *.
apply card_rem with (M1 := m1) (a0 := n0); auto.
intros n ndifn0.
elim (sumbool_of_bool (h1 n0 n)); intro h1n0n.
apply (H_col2 n).
split; auto.
left; split; auto.
inversion_clear H_cardsons_m1; inversion H0; intro m1n; elim (H1 n).
absurd (h1 n0 n = true /\ m1 n = white); auto.
apply (not_true_and_white M m1 h1 n n0); auto.
apply (H_col2 n); auto.
intros nb H_ind m1' h1' n0 H_cardsons_m1' m2' h2' g H_card_m1' m1n0 m2n0
 H_grey.
elim H_grey; clear H_grey.
intros heap H_col1 H_col2.
inversion_clear H_cardsons_m1'; inversion_clear H0;
 elim (exist_updated node color (snd (M1 a0)) m1' a0).
intros m1 mark; elim mark; clear mark.
intros H_m1_m1' m1a0.
elim (exist_updated_heap (fst (M1 a0)) h1' n0 a0); intros h1 H6; elim H6;
 clear H6.
intros H_h1_h1' H6; elim H6; clear H6.
intros H_h1_h1'_bis h1n0a0.
elim (exist_updated node color (m1 a0) m2' a0); intros m2 mark; elim mark;
 clear mark.
intros H_m2_m2' m2a0.
elim (exist_updated_heap (h1 n0 a0) h2' n0 a0); intros h2 H6; elim H6;
 clear H6.
intros H_h2_h2' H6; elim H6; clear H6.
intros H_h2_h2'_bis h2n0a0.
elim (eq_dec_color (m1 a0) grey); intro m1_a0.
unfold card_color in |- *; apply card_inv with (M1 := m2).
rewrite <- (plus_Snm_nSm g nb).
unfold card_color in H_ind;
 apply H_ind with (m1 := m1) (h1 := h1) (h2 := h2) (n0 := n0); 
 auto.
apply CS with (M := M1); auto.
intro n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0.
generalize (refl_equal (M1 a0)); pattern (M1 a0) at -1 in |- *; case (M1 a0).
intros b c M1a0.
replace b with (fst (M1 a0)).
replace c with (snd (M1 a0)).
rewrite <- m1a0; rewrite <- h1n0a0; trivial.
rewrite M1a0; auto.
rewrite M1a0; auto.
intro ndifa0.
rewrite (H2 n ndifa0); rewrite <- (H_h1_h1'_bis n ndifa0);
 rewrite <- (H_m1_m1' n ndifa0); auto.
apply card_S with (M1 := m1') (a0 := a0); auto.
replace (m1' a0) with white.
discriminate.
symmetry  in |- *; apply (is_white M h1' m1' a0 n0); auto.
rewrite <- (H_m1_m1' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; assumption.
apply (H_col1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
rewrite <- (H_m2_m2' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; assumption.
apply (H_col1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
constructor.
intros n m; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto. 
intro mdifa0; rewrite <- (H_h1_h1'_bis m mdifa0);
 rewrite <- (H_h2_h2'_bis m mdifa0); auto.
intro ndifn0; rewrite <- (H_h1_h1' n m ndifn0);
 rewrite <- (H_h2_h2' n m ndifn0); auto.
intro m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; intro H6; elim H6; clear H6.
intros h1n0a0_bis m1a0_bis; absurd (m1 a0 = grey); auto.
rewrite m1a0_bis; discriminate. 
intros mdifa0 H_m; rewrite <- (H_m2_m2' m mdifa0); apply (H_col1 m);
 rewrite (H_m1_m1' m mdifa0); rewrite (H_h1_h1'_bis m mdifa0); 
 assumption.
intro m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto.
intros mdifa0 H6; elim H6; clear H6.
intros mdifn0 H6; elim H6; clear H6.
intro H_m; rewrite <- (H_m2_m2' m mdifa0); rewrite <- (H_m1_m1' m mdifa0);
 apply (H_col2 m); split; auto.
left; rewrite (H_m1_m1' m mdifa0); rewrite (H_h1_h1'_bis m mdifa0); auto.
intro H_m; rewrite <- (H_m2_m2' m mdifa0); rewrite <- (H_m1_m1' m mdifa0);
 apply (H_col2 m).
split; auto.
right; rewrite (H_h1_h1'_bis m mdifa0); auto.
intro n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0; rewrite m2a0; intro m1a0_bis;
 absurd (m1 a0 = grey); auto.
intros ndifa0 m2n; rewrite (H_m2_m2' n ndifa0); assumption.
intros n m2n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0; apply H_col1.
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
intro ndifa0; rewrite (H_m2_m2' n ndifa0); assumption.
generalize (refl_equal g); pattern g at -1 in |- *; case g.
intro geq0; rewrite geq0 in H_card_m1'; inversion H_card_m1';
 absurd (m1' n0 = grey); auto.
intros nb' gSnb'.
rewrite <- gSnb'.
rewrite (pred_plus_S g nb); unfold card_color in |- *.
apply card_S with (M1 := m2) (a0 := a0).
unfold card_color in H_ind;
 apply H_ind with (m1 := m1) (h1 := h1) (h2 := h2) (n0 := n0); 
 auto.
apply CS with (M := M1); auto.
intro n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0.
generalize (refl_equal (M1 a0)); pattern (M1 a0) at -1 in |- *; case (M1 a0).
intros b c M1a0.
replace b with (fst (M1 a0)).
replace c with (snd (M1 a0)).
rewrite <- m1a0; rewrite <- h1n0a0; trivial.
rewrite M1a0; auto.
rewrite M1a0; auto.
intro ndifa0; rewrite (H2 n ndifa0); rewrite <- (H_h1_h1'_bis n ndifa0);
 rewrite <- (H_m1_m1' n ndifa0); auto.
apply card_inv with (M1 := m1'); auto.
intros n m1'n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0; assumption.
intro ndifa0; rewrite <- (H_m1_m1' n ndifa0); assumption.
intro n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0; intro m1'a0; absurd (m1' a0 = grey); auto.
replace (m1' a0) with white.
discriminate.
symmetry  in |- *; apply (is_white M h1' m1' a0 n0); auto.
intros ndifa0 m1'n; rewrite <- (H_m1_m1' n ndifa0); assumption.
rewrite <- (H_m1_m1' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; assumption.
apply (H_col1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
rewrite <- (H_m2_m2' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; assumption.
apply (H_col1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
constructor.
intros n m; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto. 
intro mdifa0; rewrite <- (H_h1_h1'_bis m mdifa0);
 rewrite <- (H_h2_h2'_bis m mdifa0); auto.
intro ndifn0; rewrite <- (H_h1_h1' n m ndifn0);
 rewrite <- (H_h2_h2' n m ndifn0); auto.
intro m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; intro H6; elim H6; clear H6.
intros h1n0a0_bis m1a0_bis; absurd (h1 n0 m = true /\ m1 m = white); auto.
elim H3.
generalize (refl_equal (M1 a0)); pattern (M1 a0) at -1 in |- *; case (M1 a0).
intros b c M1a0; split.
replace b with (fst (M1 a0)).
rewrite <- h1n0a0; assumption.
rewrite M1a0; auto.
replace c with (snd (M1 a0)).
rewrite <- m1a0; assumption.
rewrite M1a0; auto.
rewrite meqa0; auto.
intros mdifa0 H6; elim H6; clear H6.
intros h1n0m m1m.
rewrite <- (H_m2_m2' m mdifa0).
apply (H_col1 m).
rewrite (H_h1_h1'_bis m mdifa0); rewrite (H_m1_m1' m mdifa0); split;
 assumption.
intros m H6; elim H6; clear H6.
intros mdifn0 H6; elim H6; clear H6.
intro H6; elim H6; clear H6.
intros h1n0m m1m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto.
intro mdifa0; rewrite <- (H_m1_m1' m mdifa0); rewrite <- (H_m2_m2' m mdifa0);
 apply (H_col2 m).
split; auto.
left; rewrite (H_h1_h1'_bis m mdifa0); rewrite (H_m1_m1' m mdifa0); split;
 assumption.
intro h1n0m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto.
intro mdifa0; rewrite <- (H_m1_m1' m mdifa0); rewrite <- (H_m2_m2' m mdifa0);
 apply (H_col2 m).
split; auto.
right; rewrite (H_h1_h1'_bis m mdifa0); assumption.
intros n ndifa0; symmetry  in |- *; apply (H_m2_m2' n); assumption.
rewrite m2a0; assumption.
apply H_col1.
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
rewrite gSnb'; auto with arith.
Qed.

Lemma greynode_card_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 (exists g : nat, card_color grey (mk s) g) ->
 hp t = hp s ->
 grey_node_case (mk s) (mk t) (hp s) ->
 exists g : nat, card_color grey (mk t) g.

intros s t cardw_s cardg_s heap greynode; elim greynode; clear greynode.
intros g0 mksg0 mktg0 H_col mkseqmkt.
cut
 (exists M : node -> bool * color,
    (forall n : node, M n = (hp s g0 n, mk s n))).
intro H2; elim H2; clear H2.
intros M H_M; elim cardw_s; clear cardw_s.
intros w cardw_s; elim cardg_s; clear cardg_s.
intros g cardg_s.
cut
 (exists nb : nat,
    card _ _
      (fun p : bool * color =>
       match p with
       | (b, c) => b = true /\ c = white
       end) M nb /\ nb <= w).
intro H2; elim H2; clear H2.
intros nbsons H_nbsons; elim H_nbsons; clear H_nbsons.
intros H_cardsons le_nbsons_w.
cut (card_sons g0 white (mk s) (hp s) nbsons).
intro card_sons.
exists (pred (g + nbsons)).
apply
 card_grey_marknode with (n0 := g0) (m1 := mk s) (h1 := hp s) (h2 := hp t);
 auto.
rewrite mktg0; discriminate.
constructor; auto.
rewrite heap; auto.
apply CS with (M := M); auto.
apply
 include_card_bis
  with (P := fun c : color => c = white) (M := mk s) (nb := w); 
 auto.
exists (hp s rt g0, mk s g0).
intro H2; elim H2; clear H2.
intros hrtg0 mksg02; absurd (mk s g0 = white); auto.
rewrite mksg0; discriminate.
unfold prop_dec2 in |- *.
intro c; case c; intros b c0; elim (sumbool_of_bool b).
elim (eq_dec_color c0 white).
intros c0_w b_t; left; auto.
intros c0_notw b_t; right; intro H2; elim H2; clear H2.
intros bt c0w; absurd (c0 = white); auto.
intro b_f; right; intro H2; elim H2; clear H2.
intros b_t c0_w; apply (eq_true_false_abs b); auto.
intros n; generalize (refl_equal (M n)); pattern (M n) at -1 in |- *;
 case (M n); intros b c M_n.
intro H2; elim H2; clear H2.
intros b_t c_w; replace (mk s n) with c; auto.
replace c with (snd (M n)).
rewrite (H_M n); auto.
rewrite M_n; auto.
exists (fun n : node => (hp s g0 n, mk s n)); auto.
Qed.

Hint Resolve greynode_card_white.

Lemma ex_gccall_grey :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 (exists g : nat, card_color grey (mk s) g) ->
 gc_call s t -> exists g : nat, card_color grey (mk t) g.

intros s t cardw_s cardg_s gccall; elim gccall; clear gccall.
intros ctls ctlt heap H_col init; elim cardg_s; clear cardg_s.
intros g cardg_s; exists 1; eauto.
intros ctls ctlt heap greynode; eauto.
intros ctls ctlt heap H_col m mksm upd_col; elim cardg_s; clear cardg_s.
intros g cardg_s; exists g; unfold card_color in |- *;
 apply card_inv with (M1 := mk s); auto.
elim upd_col; clear upd_col.
intros mark mktm n mksn; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n ndifm); assumption.
intros n mksn; absurd (mk s n = grey); auto.
Qed.


Lemma ex_marknode_grey :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 (exists g : nat, card_color grey (mk s) g) ->
 mark_node s t -> exists g : nat, card_color grey (mk t) g.

intros s t cardw_s cardg_s marknode; elim marknode; clear marknode.
intros ctls ctlt heap greynode; eauto.
Qed.


Lemma gcstop_grey :
 forall (s t : state) (g : nat),
 card_color grey (mk s) g -> gc_stop s t -> card_color grey (mk t) g.

intros s t g card_s gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcstop_grey.

Lemma ex_gcstop_grey :
 forall s t : state,
 (exists g : nat, card_color grey (mk s) g) ->
 gc_stop s t -> exists g : nat, card_color grey (mk t) g.

intros s t card_s gcstop; elim card_s; clear card_s.
intros g card_s; exists g; eauto.
Qed.


Lemma gcfree_grey :
 forall (s t : state) (g : nat),
 card_color grey (mk s) g -> gc_free s t -> card_color grey (mk t) g.

intros s t g card_s gcfree; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm upd_col.
unfold card_color in |- *; apply card_inv with (M1 := mk s); auto.
intros n mksn; apply (gcfree_notgreys_notgreyt s t); auto.
apply (free_no_grey_but_white s t) with (m := m); auto.
intros n mksn; apply (gcfree_greys_greyt s t); auto.
apply (free_no_grey_but_white s t) with (m := m); auto.
Qed.

Hint Resolve gcfree_grey.

Lemma ex_gcfree_grey :
 forall s t : state,
 (exists g : nat, card_color grey (mk s) g) ->
 gc_free s t -> exists g : nat, card_color grey (mk t) g.

intros s t card_s gcfree; elim card_s; clear card_s.
intros g card_s; exists g; eauto.
Qed.


Lemma gcfree1_grey :
 forall (s t : state) (g : nat),
 card_color grey (mk s) g -> gc_free1 s t -> card_color grey (mk t) g.

intros s t g card_s gcfree1.
unfold card_color in |- *; apply card_inv with (M1 := mk s); auto.
intros m mksm; apply (gcfree1_notgreys_notgreyt s t); assumption.
intros m mksm; apply (gcfree1_greys_greyt s t); assumption.
Qed.

Hint Resolve gcfree1_grey.

Lemma ex_gcfree1_grey :
 forall s t : state,
 (exists g : nat, card_color grey (mk s) g) ->
 gc_free1 s t -> exists g : nat, card_color grey (mk t) g.

intros s t card_s gcfree1; elim card_s; clear card_s.
intros g card_s; exists g; eauto.
Qed.


Lemma gcend_grey :
 forall (s t : state) (g : nat),
 card_color grey (mk s) g -> gc_end s t -> card_color grey (mk t) g.

intros s t g card_s gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcend_grey.


Lemma ex_gcend_grey :
 forall s t : state,
 (exists g : nat, card_color grey (mk s) g) ->
 gc_end s t -> exists g : nat, card_color grey (mk t) g.

intros s t card_s gcend; elim card_s; clear card_s.
intros g card_s; exists g; eauto.
Qed.


End grey_card.

Hint Immediate init_grey.
Hint Immediate add_grey.
Hint Immediate remove_grey.
Hint Immediate alloc_grey.
Hint Immediate gcstop_grey.
Hint Immediate gcfree_grey.
Hint Immediate gcfree1_grey.
Hint Immediate gcend_grey.
Hint Immediate ex_init_grey.
Hint Immediate ex_add_grey.
Hint Immediate ex_remove_grey.
Hint Immediate ex_alloc_grey.
Hint Immediate ex_gccall_grey.
Hint Immediate ex_marknode_grey.
Hint Immediate ex_gcstop_grey.
Hint Immediate ex_gcfree_grey.
Hint Immediate ex_gcfree1_grey.
Hint Immediate ex_gcend_grey.
Hint Resolve initcol_grey.