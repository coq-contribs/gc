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
(*                              white_card.v                                *)
(****************************************************************************)

Section white_card.

Require Export card_facts.
Require Export parameters_card.
Require Export lemme_arith.
Require Export lemma_step.
Require Export Arith.
Require Export Peano_dec.
Require Export Bool.
Require Export safety.

Notation Card := (card _ _) (only parsing).

Lemma init_white :
 forall s : state, init_state s -> card_color white (mk s) 0.

intros s init; elim init; clear init.
intros ctls init; elim init; clear init.
intros mark heap; elim mark; clear mark.
intros mksrt mark; constructor.
intro n; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt; rewrite mksrt; discriminate.
intro ndifrt; rewrite (mark n ndifrt); discriminate.
Qed.

Hint Resolve init_white.

Lemma ex_init_white :
 forall s : state, init_state s -> exists w : nat, card_color white (mk s) w.

intros s init; exists 0; eauto.
Qed.

Lemma add_white :
 forall (s t : state) (w : nat),
 card_color white (mk s) w ->
 add_edge s t ->
 card_color white (mk t) w \/ card_color white (mk t) (pred w).

intros s t w card_s addedge; elim addedge; clear addedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark.
elim mark; clear mark.
intro cas1; elim cas1; clear cas1.
intros mksn1 eqmk; left; rewrite eqmk; assumption.
intro cas; elim cas; clear cas.
intro cas2; elim cas2; clear cas2.
intros mksn1 eqmk; elim eqmk; clear eqmk.
intros mksn2 eqmk; left; rewrite eqmk; assumption.
intro cas3; elim cas3; clear cas3.
intros mksn1 mk2; elim mk2; clear mk2.
intros mksn2 upd_col; elim upd_col; clear upd_col.
intros H_col mktn2.
right.
unfold card_color in |- *.
apply card_rem with (M1 := mk s) (a0 := n2); auto.
rewrite mktn2; discriminate.
Qed.

Hint Resolve add_white.

Lemma ex_add_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 add_edge s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s addedge; elim addedge; clear addedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt add mark.
elim card_s; clear card_s.
intros w card_s; elim add; clear add.
intros H_heap1 H_heap2; elim H_heap2; clear H_heap2.
intros H_heap2 htn1n2; elim mark; clear mark.
intro cas1; elim cas1; clear cas1.
intros mksn1 eqmk; rewrite eqmk; exists w; assumption.
intro cas; elim cas; clear cas.
intro cas2; elim cas2; clear cas2.
intros mksn1 eqmk; elim eqmk; clear eqmk.
intros mksn2 eqmk; rewrite eqmk; exists w; assumption.
intro cas3; elim cas3; clear cas3.
intros mksn1 mk2; elim mk2; clear mk2.
intros mksn2 upd_col; elim upd_col; clear upd_col.
intros H_col mktn2; exists (pred w); unfold card_color in |- *.
apply card_rem with (M1 := mk s) (a0 := n2); auto.
rewrite mktn2; discriminate.
Qed.

Lemma remove_white :
 forall (s t : state) (w : nat),
 card_color white (mk s) w -> remove_edge s t -> card_color white (mk t) w.

intros s t w card_s removeedge.
elim removeedge; clear removeedge.
intros n1 n2 acces_n1_s acces_n2_s ctls ctlt remove mark.
rewrite mark; assumption.
Qed.

Hint Resolve remove_white.

Lemma ex_remove_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 remove_edge s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s removeedge.
elim card_s; clear card_s.
intros w card_s; exists w; eauto.
Qed.

Lemma alloc_white :
 forall (s t : state) (w : nat),
 card_color white (mk s) w -> alloc s t -> card_color white (mk t) w.

intros s t w card_s alloc; unfold card_color in |- *.
apply card_inv with (M1 := mk s); auto.
intros n mksn.
apply (alloc_notwhites_notwhitet s t); assumption.
intros n mksn.
apply (alloc_whites_whitet s t); assumption.
Qed.

Hint Resolve alloc_white.

Lemma ex_alloc_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 alloc s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s alloc; elim card_s; clear card_s.
intros w card_s; exists w; eauto.
Qed.

Lemma initcol_white :
 forall (s t : state) (b : nat),
 rt_grey_or_black s ->
 init_color (mk s) (mk t) ->
 card_color black (mk s) b ->
 (forall n : node, mk s n = black \/ mk s n = free) ->
 card_color white (mk t) (pred b).

unfold rt_grey_or_black in |- *.
intros s t b H_rt init cardb_s H_col.
elim init; clear init.
intros mktrt mark; elim mark; clear mark.
intros mark1 mark2; elim (exist_updated node color (mk t rt) (mk s) rt).
intros mk' mark; elim mark; clear mark.
intros mark mk'rt.
cut (card_color black mk' (pred b)).
intro card_mk'.
cut (exists nb' : nat, card_color white (mk t) nb' /\ nb' <= pred b).
intro H_nb'; elim H_nb'; clear H_nb'.
intros nb' H_nb'; elim H_nb'; clear H_nb'.
intros card_mkt le_nb'_predb.
cut (exists nb'' : nat, card_color black mk' nb'' /\ nb'' <= nb').
intro H_nb''; elim H_nb''; clear H_nb''.
intros nb'' H_nb''; elim H_nb''; clear H_nb''.
intros cardb_mk' le_nb''_nb'.
cut (nb'' = pred b).
intro nb''_eq_predb; rewrite nb''_eq_predb in le_nb''_nb'.
cut (nb' = pred b); auto with arith.
intro nb'_eq_predb; rewrite <- nb'_eq_predb; assumption.
unfold card_color in card_mk'; unfold card_color in cardb_mk'.
apply
 unicity_card
  with
    (M := mk')
    (nb' := pred b)
    (nb := nb'')
    (P := fun c : color => c = black); assumption.
unfold card_color in |- *.
apply include_card_bis with (P := fun c : color => c = white) (M := mk t);
 auto.
exists grey; discriminate.
unfold prop_dec2 in |- *.
intro c; apply (eq_dec_color c black).
intro n; elim (eq_dec_node n rt).
intro neqrt; rewrite neqrt.
intro mk'rt2.
absurd (mk' rt = black); try assumption.
rewrite mk'rt; rewrite mktrt; discriminate.
intros ndifrt mk'n; rewrite <- (mark n ndifrt) in mk'n.
apply mark1; assumption.
unfold card_color in |- *.
apply include_card_bis with (P := fun c : color => c = black) (M := mk');
 auto.
exists grey; discriminate.
unfold prop_dec2 in |- *; intro c.
apply (eq_dec_color c white).
intros n mktn; elim (eq_dec_node n rt).
intro neqrt.
rewrite neqrt in mktn.
absurd (mk t rt = white); try assumption.
rewrite mktrt; discriminate.
intro ndifrt.
rewrite <- (mark n ndifrt).
elim (eq_dec_color (mk s n) black); auto.
intro mksn.
absurd (mk t n = white); try assumption.
replace (mk t n) with free.
discriminate.
rewrite (mark2 n); try assumption.
elim (H_col n); intro mksn2; auto.
absurd (mk s n = black); assumption.
unfold card_color in |- *.
apply card_rem with (M1 := mk s) (a0 := rt); auto.
elim H_rt; auto.
intro mksrt; absurd (mk s rt = grey); auto.
elim (H_col rt); intro mksrt2; rewrite mksrt2; discriminate.
rewrite mk'rt; rewrite mktrt; discriminate.
Qed.

Hint Resolve initcol_white.

Lemma card_white_marknode :
 forall (nb : nat) (m1 : marking) (h1 : heap) (n0 : node),
 card_sons n0 white m1 h1 nb ->
 forall (m2 : marking) (h2 : heap) (w : nat),
 card_color white m1 w ->
 m1 n0 = grey ->
 m2 n0 = black ->
 grey_white_sons m1 m2 h1 h2 n0 -> card_color white m2 (w - nb).

simple induction nb; clear nb.
intros m1 h1 n0 H_cardsons_m1 m2 h2 w H_card_m1 m1n0 m2n0 H_grey.
rewrite <- (minus_n_O w).
elim H_grey; clear H_grey.
intros heap H_col1 H_col2.
unfold card_color in |- *.
apply card_inv with (nb := w) (M1 := m1); auto.
intros n m1n.
elim (eq_dec_node n n0).
intro neqn0.
rewrite neqn0; rewrite m2n0; discriminate.
intro ndifn0.
elim (sumbool_of_bool (h1 n0 n)); intro h1n0n.
replace (m2 n) with (m1 n); auto.
replace (m2 n) with (m1 n); auto.
intros n m1n; elim (eq_dec_node n0 n).
intro neqn0; rewrite <- neqn0 in m1n; absurd (m1 n0 = white); auto.
rewrite m1n0; discriminate.
intro ndifn0.
elim (sumbool_of_bool (h1 n0 n)); intro h1n0n.
elim H_cardsons_m1; clear H_cardsons_m1.
intros M Mn H_cardsons_m1.
inversion_clear H_cardsons_m1.
absurd (h1 n0 n = true /\ m1 n = white); auto.
apply (not_true_and_white M m1 h1 n n0); auto.
replace (m2 n) with (m1 n); auto.
intros nb H_ind m1' h1' n0 H_cardsons_1 m2' h2' w H_card_1 m1n0 m2n0 H_grey.
inversion_clear H_cardsons_1; inversion_clear H0.
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
intros H_h2_h2' H6.
elim H6; clear H6.
intros H_h2_h2'_bis h2n0a0.
elim H_grey; clear H_grey.
intros heap H_heap1 H_heap2.
elim (eq_dec_color (m1 a0) white); intro m1_a0.
rewrite (minus_pred w nb).
unfold card_color in |- *.
apply card_rem with (M1 := m2) (a0 := a0).
unfold card_color in H_ind.
apply H_ind with (m1 := m1) (h1 := h1) (h2 := h2) (n0 := n0); auto.
apply CS with (M := M1); auto.
intro n; elim (eq_dec_node n a0).
intro neqa0.
rewrite neqa0.
generalize (refl_equal (M1 a0)); pattern (M1 a0) at -1 in |- *; case (M1 a0);
 intros b c M1a0.
replace b with (fst (M1 a0)).
replace c with (snd (M1 a0)).
rewrite <- m1a0; rewrite <- h1n0a0; trivial.
rewrite M1a0; auto.
rewrite M1a0; auto.
intro ndifa0.
rewrite (H2 n ndifa0); rewrite <- (H_h1_h1'_bis n ndifa0);
 rewrite <- (H_m1_m1' n ndifa0); auto.
apply card_inv with (M1 := m1'); auto.
intros n m1'n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0 in m1'n.
absurd (m1' a0 = white); auto.
apply (is_white M h1' m1' a0 n0); auto.
intro ndifa0; rewrite <- (H_m1_m1' n ndifa0); auto.
intros n m1'n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0; assumption.
intro ndifa0; rewrite <- (H_m1_m1' n ndifa0); auto.
rewrite <- (H_m1_m1' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; rewrite m2n0; discriminate.
apply (H_heap1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
rewrite <- (H_m2_m2' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; rewrite m2n0; discriminate.
apply (H_heap1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
constructor.
intros n m; elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto. 
intro mdifa0.
rewrite <- (H_h1_h1'_bis m mdifa0).
rewrite <- (H_h2_h2'_bis m mdifa0).
auto.
intro ndifn0.
rewrite <- (H_h1_h1' n m ndifn0).
rewrite <- (H_h2_h2' n m ndifn0).
auto.
intro m; elim (eq_dec_node m a0).
intros meqa0.
rewrite meqa0.
intro H_m.
absurd (h1 n0 m = true /\ m1 m = white); auto.
elim H3.
generalize (refl_equal (M1 a0)); pattern (M1 a0) at -1 in |- *; case (M1 a0).
intros b c M1a0; elim H_m; clear H_m.
intros h1n0a0_bis m1a0_bis; split.
replace b with (fst (M1 a0)).
rewrite <- h1n0a0; assumption.
rewrite M1a0; auto.
replace c with (snd (M1 a0)).
rewrite <- m1a0; assumption.
rewrite M1a0; auto.
rewrite meqa0; assumption.
intros mdifa0 H6; elim H6; clear H6.
intros h1n0m m1m.
rewrite <- (H_m2_m2' m mdifa0).
apply (H_heap1 m).
rewrite (H_h1_h1'_bis m mdifa0).
rewrite (H_m1_m1' m mdifa0).
split; assumption.
intros m H6; elim H6; clear H6.
intros mdifn0 H6; elim H6; clear H6.
intro H6; elim H6; clear H6.
intros h1n0m m1m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0 in m1m.
absurd (m1 a0 = white); assumption.
intro mdifa0.
rewrite <- (H_m1_m1' m mdifa0).
rewrite <- (H_m2_m2' m mdifa0).
apply (H_heap2 m).
split; auto.
left.
rewrite (H_h1_h1'_bis m mdifa0).
rewrite (H_m1_m1' m mdifa0).
split; assumption.
intro h1n0m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto.
intro mdifa0.
rewrite <- (H_m1_m1' m mdifa0).
rewrite <- (H_m2_m2' m mdifa0).
apply (H_heap2 m).
split; auto.
right; rewrite (H_h1_h1'_bis m mdifa0); assumption.
intros n ndifa0.
symmetry  in |- *; apply (H_m2_m2' n); assumption.
rewrite m2a0; assumption.
rewrite (H_heap1 a0); auto.
discriminate.
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
unfold card_color in |- *; apply card_inv with (M1 := m2).
rewrite (pred_S_minus w nb).
unfold card_color in H_ind.
apply H_ind with (m1 := m1) (h1 := h1) (h2 := h2) (n0 := n0); auto.
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
rewrite (H2 n ndifa0).
rewrite <- (H_h1_h1'_bis n ndifa0).
rewrite <- (H_m1_m1' n ndifa0).
auto.
apply card_rem with (M1 := m1') (a0 := a0); auto.
apply (is_white M h1' m1' a0 n0); auto.
rewrite <- (H_m1_m1' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; rewrite m2n0; discriminate.
apply (H_heap1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
rewrite <- (H_m2_m2' n0); auto.
intro n0eqa0; absurd (m2' a0 = grey).
rewrite <- n0eqa0; rewrite m2n0; discriminate.
apply (H_heap1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
constructor.
intros n m.
elim (eq_dec_node n n0).
intro neqn0; rewrite neqn0; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto. 
intro mdifa0; rewrite <- (H_h1_h1'_bis m mdifa0);
 rewrite <- (H_h2_h2'_bis m mdifa0); auto.
intro ndifn0; rewrite <- (H_h1_h1' n m ndifn0);
 rewrite <- (H_h2_h2' n m ndifn0); auto.
intro m; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; intro H6; elim H6; clear H6.
intros h1n0a0_bis m1a0_bis; absurd (m1 a0 = white); auto.
intros mdifa0 H_m; rewrite <- (H_m2_m2' m mdifa0).
apply (H_heap1 m).
rewrite (H_h1_h1'_bis m mdifa0); rewrite (H_m1_m1' m mdifa0); assumption.
intros m H6; elim (eq_dec_node m a0).
intro meqa0; rewrite meqa0; auto.
intro mdifa0; elim H6; clear H6.
intros mdifn0 H6; elim H6; clear H6.
intro H6; elim H6; clear H6.
intros h1n0m m1m; rewrite <- (H_m1_m1' m mdifa0);
 rewrite <- (H_m2_m2' m mdifa0); apply (H_heap2 m).
split; auto.
left; rewrite (H_h1_h1'_bis m mdifa0); rewrite (H_m1_m1' m mdifa0); split;
 auto.
intro h1n0m; rewrite <- (H_m1_m1' m mdifa0); rewrite <- (H_m2_m2' m mdifa0);
 apply (H_heap2 m).
split; auto.
right; rewrite (H_h1_h1'_bis m mdifa0); assumption.
intros n m2n.
elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0; replace (m2' a0) with grey.
discriminate.
symmetry  in |- *; apply (H_heap1 a0).
split.
apply (is_true M h1' m1' a0 n0); auto.
apply (is_white M h1' m1' a0 n0); auto.
intro ndifa0; rewrite (H_m2_m2' n ndifa0); assumption.
intros n m2n; elim (eq_dec_node n a0).
intro neqa0; rewrite neqa0 in m2n; absurd (m2 a0 = white); auto.
rewrite m2a0; assumption.
intro ndifa0; rewrite (H_m2_m2' n ndifa0); assumption.
Qed.

Lemma greynode_card_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 hp s = hp t ->
 grey_node_case (mk s) (mk t) (hp s) ->
 exists w : nat, card_color white (mk t) w.

intros s t card_s heap H_grey; elim H_grey; clear H_grey.
intros g mksg mktg H_mark1 H_mark2.
cut
 (exists M : node -> bool * color,
    (forall n : node, M n = (hp s g n, mk s n))).
intro H2; elim H2; clear H2.
intros M H_M; elim card_s; clear card_s.
intros w card_s.
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
cut (card_sons g white (mk s) (hp s) nbsons).
intro card_sons.
exists (w - nbsons).
apply
 card_white_marknode
  with (m1 := mk s) (h1 := hp s) (h2 := hp t) (nb := nbsons) (n0 := g); 
 auto.
constructor; auto.
rewrite heap; auto.
apply CS with (M := M); auto.
apply
 include_card_bis
  with (P := fun c : color => c = white) (M := mk s) (nb := w); 
 auto.
exists (hp s rt g, mk s g).
intro H2; elim H2; clear H2.
intros hrtg mksg2; absurd (mk s g = white); auto.
rewrite mksg; discriminate.
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
exists (fun n : node => (hp s g n, mk s n)); auto.
Qed.

Hint Resolve greynode_card_white.

Lemma ex_gccall_white :
 forall s t : state,
 rt_grey_or_black s ->
 (exists b : nat, card_color black (mk s) b) ->
 (exists w : nat, card_color white (mk s) w) ->
 gc_call s t -> exists w : nat, card_color white (mk t) w.

intros s t safety_prop cardb_s cardw_s gccall; elim cardb_s; clear cardb_s.
intros b0 cardb_s; elim gccall; clear gccall.
intros ctls ctlt heap H_col init; exists (pred b0); eauto.
intros ctls ctlt heap H_grey; eauto.
intros ctls ctlt heap H_col m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; elim cardw_s; clear cardw_s.
intros w cardw_s; exists (pred w); unfold card_color in |- *.
apply card_rem with (M1 := mk s) (a0 := m); auto.
rewrite mktm; discriminate.
Qed.

Lemma ex_marknode_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 mark_node s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s marknode; elim marknode; clear marknode.
intros ctls ctlt heap H_grey; eauto.
Qed.

Lemma gcstop_white :
 forall (s t : state) (w : nat),
 card_color white (mk s) w -> gc_stop s t -> card_color white (mk t) w.

intros s t w card_s gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcstop_white.

Lemma ex_gcstop_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 gc_stop s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s gcstop; elim card_s; clear card_s.
intros w card_s; exists w; eauto.
Qed.


Lemma gcfree_white :
 forall (s t : state) (w : nat),
 card_color white (mk s) w -> gc_free s t -> card_color white (mk t) (pred w).

intros s t w card_s gcfree; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; unfold card_color in |- *;
 apply card_rem with (M1 := mk s) (a0 := m); auto.
rewrite mktm; discriminate.
Qed.

Hint Resolve gcfree_white.

Lemma ex_gcfree_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 gc_free s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s gcfree; elim card_s; clear card_s.
intros w card_s; eauto.
Qed.


Lemma gcfree1_white :
 forall (s t : state) (w : nat),
 card_color white (mk s) w ->
 gc_free1 s t -> card_color white (mk t) (pred w).

intros s t w card_s gcfree1; elim gcfree1; clear gcfree1.
intros ctls ctlt heap n mksn upd_col; elim upd_col; clear upd_col.
intros mark mktn; unfold card_color in |- *.
apply card_rem with (M1 := mk s) (a0 := n); auto.
rewrite mktn; discriminate.
Qed.

Hint Resolve gcfree1_white.

Lemma ex_gcfree1_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 gc_free1 s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s gcfree1; elim card_s; clear card_s.
intros w card_s; exists (pred w); eauto.
Qed.


Lemma gcend_white :
 forall (s t : state) (w : nat),
 card_color white (mk s) w -> gc_end s t -> card_color white (mk t) w.

intros s t w card_s gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcend_white.

Lemma ex_gcend_white :
 forall s t : state,
 (exists w : nat, card_color white (mk s) w) ->
 gc_end s t -> exists w : nat, card_color white (mk t) w.

intros s t card_s gcend; elim card_s; clear card_s.
intros w card_s; exists w; eauto.
Qed.


End white_card.

Hint Immediate init_white.
Hint Immediate add_white.
Hint Immediate remove_white.
Hint Immediate alloc_white.
Hint Immediate gcstop_white.
Hint Immediate gcfree_white.
Hint Immediate gcfree1_white.
Hint Immediate gcend_white.
Hint Immediate ex_init_white.
Hint Immediate ex_add_white.
Hint Immediate ex_remove_white.
Hint Immediate ex_alloc_white.
Hint Immediate ex_gccall_white.
Hint Immediate ex_marknode_white.
Hint Immediate ex_gcstop_white.
Hint Immediate ex_gcfree_white.
Hint Immediate ex_gcfree1_white.
Hint Immediate ex_gcend_white.
Hint Resolve initcol_white.