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
(*                                mesure.v                                  *)
(****************************************************************************)

Section mesure.

Require Export white_card.
Require Export grey_card.

Notation Card := (card _ _) (only parsing).

Inductive mesure (m : marking) : nat -> Prop :=
    mesur :
      forall w g : nat,
      card_color grey m g -> card_color white m w -> mesure m (g + w).

Lemma init_mesure : forall s : state, init_state s -> mesure (mk s) 0.

intros s init_state; replace 0 with (0 + 0); auto with arith.
constructor; eauto.
Qed.

Hint Resolve init_mesure.

Lemma init_ex_mesure :
 forall s : state, init_state s -> exists nb : nat, mesure (mk s) nb.

intros s init_state; exists 0; eauto.
Qed.

Lemma add_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> add_edge s t -> mesure (mk t) nb.
         
intros s t nb mes_s add; elim add; clear add.
intros n m accsn accsm cts ctt add mark; unfold marking_add in mark;
 elim mark; clear mark.
intro cas1; elim cas1; clear cas1.
intros mksn eqmk; rewrite eqmk; assumption.
intro cas; elim cas; clear cas.
intro cas2; elim cas2; clear cas2.
intros mksn eqmk; elim eqmk; clear eqmk.
intros mksm eqmk; rewrite eqmk; assumption.
intro cas3; elim cas3; clear cas3.
intros mksn mk2; elim mk2; clear mk2.
intros mksm updcol; inversion mes_s; elim (eq_nat_dec w 0).
intro weqO; absurd (card_color white (mk s) 0).
intro cards; inversion cards; absurd (mk s m = white); auto.
rewrite <- weqO; assumption.
intro wdifO; replace (g + w) with (S g + pred w).
elim updcol; clear updcol.
intros mkeq mktm; apply (mesur (mk t)); unfold card_color in |- *.
apply card_S with (M1 := mk s) (a0 := m); auto.
rewrite mksm; discriminate.
apply card_rem with (M1 := mk s) (a0 := m); auto.
rewrite mktm; discriminate.
rewrite (plus_S_pred g w); auto.
Qed.

Hint Resolve add_mesure.

Lemma add_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 add_edge s t -> exists nb : nat, mesure (mk t) nb.

intros s t H addedge; elim H; clear H.
intros nb H_mes; exists nb; eauto.
Qed.

Hint Resolve add_ex_mesure.

Lemma remove_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> remove_edge s t -> mesure (mk t) nb.

intros s t nb mes_s removeedge; elim removeedge; clear removeedge.
intros n m accsn accsm cts ctt remove mkeq; rewrite mkeq; assumption.
Qed.

Hint Resolve remove_mesure.

Lemma remove_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 remove_edge s t -> exists nb : nat, mesure (mk t) nb.

intros s t H removeedge; elim H; clear H.
intros nb H_mes; exists nb; eauto.
Qed.

Hint Resolve remove_ex_mesure.


Lemma alloc_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> alloc s t -> mesure (mk t) nb.

intros s t nb mes_s alloc; inversion mes_s; apply (mesur (mk t)); eauto.
Qed.

Hint Resolve alloc_mesure.

Lemma alloc_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 alloc s t -> exists nb : nat, mesure (mk t) nb.

intros s t H alloc; elim H; clear H.
intros nb H_mes; exists nb; eauto.
Qed.

Hint Resolve alloc_ex_mesure.

Lemma gccall_mesure :
 forall (s t : state) (nb : nat),
 gc_call s t ->
 mesure (mk s) 0 \/ (mesure (mk s) nb -> nb <> 0 /\ mesure (mk t) (pred nb)).

intros s t nb gccall; elim gccall; clear gccall.
intros ctls ctlt heap H_mark init; left; replace 0 with (0 + 0); auto.
apply (mesur (mk s)); constructor; intro n; elim (H_mark n); intro mksn;
 rewrite mksn; discriminate.
intros ctls ctlt heap greynode; elim greynode; clear greynode.
intros g mksg mktg H_col1 H_col2; right; intro mes_s; split.
intro nbeq0; rewrite nbeq0 in mes_s; inversion mes_s.
cut (g0 = 0).
intro g0eq0; rewrite g0eq0 in H0; inversion H0; absurd (mk s g = grey); auto.
rewrite (plus_comm g0 w) in H; apply (plus_O_O w g0); auto.
inversion mes_s; clear mes_s.
cut
 (exists M : node -> bool * color,
    (forall n : node, M n = (hp s g n, mk s n))).
intro H2; elim H2; clear H2.
intros M H_M.
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
rewrite (pred_plus_minus nbsons g0 w); auto.
apply (mesur (mk t)).
apply
 card_grey_marknode with (n0 := g) (m1 := mk s) (h1 := hp s) (h2 := hp t);
 auto.
rewrite mktg; discriminate.
constructor; auto.
rewrite heap; auto.
apply
 card_white_marknode
  with (m1 := mk s) (h1 := hp s) (h2 := hp t) (nb := nbsons) (n0 := g); 
 auto.
constructor; auto.
rewrite heap; auto.
intro g0eq0; rewrite g0eq0 in H; inversion H; absurd (mk s g = grey); auto.
apply CS with (M := M); auto.
unfold card_color in H0.
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
intros ctls ctlt heap H_mark m mksm upd_col; right; intro mes_s; split.
intro nbeqO; absurd (mesure (mk s) nb); auto.
rewrite nbeqO; intro mes_s_O; inversion mes_s_O; clear mes_s_O.
generalize (refl_equal w); pattern w at -1 in |- *; case w.
intro weqO; rewrite weqO in H1; inversion H1; absurd (mk s m = white); auto.
intros n weqSn; absurd (w = S n); auto.
cut (w = 0).
intro weqO; rewrite weqO; auto with arith.
apply (plus_O_O g w); assumption.
elim upd_col; clear upd_col.
intros mark mktm.
inversion mes_s; clear mes_s; elim (eq_nat_dec w 0).
intro wO; absurd (card_color white (mk s) 0).
intro cards; inversion cards; absurd (mk s m = white); auto.
rewrite <- wO; assumption.
intro wO; replace (pred (g + w)) with (g + pred w).
apply (mesur (mk t)).
unfold card_color in |- *; apply card_inv with (M1 := mk s); auto.
intros n mksn; elim (eq_dec_node n m).
intro neqm; rewrite neqm; rewrite mktm; discriminate.
intro ndifm; rewrite <- (mark n ndifm); assumption.
intros n mksn; absurd (mk s n = grey); auto.
unfold card_color in |- *; apply card_rem with (M1 := mk s) (a0 := m); auto.
rewrite mktm; discriminate.
symmetry  in |- *; apply (plus_pred g w); assumption.
Qed.

Lemma gccall_ex_mesure :
 forall s t : state,
 rt_grey_or_black s ->
 (exists b : nat, card_color black (mk s) b) ->
 (exists nb : nat, mesure (mk s) nb) ->
 gc_call s t -> exists nb : nat, mesure (mk t) nb.

intros s t H_rt H_black H gccall; elim H; clear H.
intros nb H_mes; elim gccall; clear gccall.
intros ctls ctlt heap H_col H_init; elim H_black; clear H_black.
intros b H_card; exists (1 + pred b).
constructor; eauto.
intros ctls ctlt heap H_grey; exists (pred nb);
 cut
  (mesure (mk s) 0 \/
   (mesure (mk s) nb -> nb <> 0 /\ mesure (mk t) (pred nb))).
intro H; elim H; clear H.
elim H_grey; clear H_grey.
intros g mksg mktg mark1 mark2 Hmes; absurd (mesure (mk s) 0); auto.
intro Hmes_O; inversion Hmes_O.
cut (g0 = 0).
intro g0eq0; rewrite g0eq0 in H0; inversion H0; absurd (mk s g = grey); auto.
rewrite (plus_comm g0 w) in H; apply (plus_O_O w g0); assumption.
intro H; elim H; auto.
apply (gccall_mesure s t nb); auto.
apply (call_exist_grey s t); auto.
intros ctls ctlt heap H_col m mksm upd_col; exists (pred nb);
 cut
  (mesure (mk s) 0 \/
   (mesure (mk s) nb -> nb <> 0 /\ mesure (mk t) (pred nb))).
intro H; elim H; clear H.
intro Hmes_O; absurd (mesure (mk s) 0); auto.
intro Hmes; inversion Hmes.
cut (w = 0).
intro weq0; rewrite weq0 in H1; inversion H1; absurd (mk s m = white); auto.
apply (plus_O_O g w); assumption.
intro H; elim H; auto.
apply (gccall_mesure s t nb); auto.
apply init_no_greys_but_white with (s := s) (t := t) (m := m); auto.
Qed.

Hint Resolve gccall_ex_mesure.

Lemma marknode_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> mark_node s t -> mesure (mk t) (pred nb).

intros s t nb mes_s marknode.
inversion mes_s; clear mes_s.
elim marknode; clear marknode.
intros ctls ctlt heap greynode; clear ctls ctlt.
elim greynode; clear greynode.
intros g0 mksg0 mktg0 H_col mkseqmkt.
cut
 (exists M : node -> bool * color,
    (forall n : node, M n = (hp s g0 n, mk s n))).
intro H2; elim H2; clear H2.
intros M H_M.
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
rewrite (pred_plus_minus nbsons g w); auto.
apply (mesur (mk t)).
apply
 card_grey_marknode with (n0 := g0) (m1 := mk s) (h1 := hp s) (h2 := hp t);
 auto.
rewrite mktg0; discriminate.
constructor; auto.
rewrite heap; auto.
apply
 card_white_marknode
  with (m1 := mk s) (h1 := hp s) (h2 := hp t) (nb := nbsons) (n0 := g0); 
 auto.
constructor; auto.
rewrite heap; auto.
intro geq0; rewrite geq0 in H; inversion H; absurd (mk s g0 = grey); auto.
apply CS with (M := M); auto.
unfold card_color in H0.
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

Hint Resolve marknode_mesure.

Lemma marknode_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 mark_node s t -> exists nb : nat, mesure (mk t) nb.

intros s t H marknode; elim H; clear H.
intros nb H_mes; exists (pred nb); eauto.
Qed.

Hint Resolve marknode_ex_mesure.

Lemma gcstop_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> gc_stop s t -> mesure (mk t) nb.

intros s t nb mes_s gcstop; elim gcstop; clear gcstop.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcstop_mesure.

Lemma gcstop_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 gc_stop s t -> exists nb : nat, mesure (mk t) nb.

intros s t H gcstop; elim H; clear H.
intros nb H_mes; exists nb; eauto.
Qed.

Hint Resolve gcstop_ex_mesure.

Lemma gcfree_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> gc_free s t -> mesure (mk t) (pred nb).

intros s t nb H_mes gcfree; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm upd_col; inversion H_mes;
 elim (eq_nat_dec w 0).
intro weqO; absurd (card_color white (mk s) 0).
intro cards; inversion cards; absurd (mk s m = white); auto.
rewrite <- weqO; assumption.
intro wdifO; replace (pred (g + w)) with (g + pred w).
apply (mesur (mk t)); unfold card_color in |- *.
apply card_inv with (M1 := mk s); auto.
intros n mksn; apply (gcfree_notgreys_notgreyt s t); auto.
apply (free_no_grey_but_white s t) with (m := m); auto.
intros n mksn; apply (gcfree_greys_greyt s t); auto.
apply (free_no_grey_but_white s t) with (m := m); auto.
elim upd_col; clear upd_col.
intros mark mktm.
apply card_rem with (M1 := mk s) (a0 := m); auto.
rewrite mktm; discriminate.
symmetry  in |- *; apply (plus_pred g w); assumption.
Qed.

Hint Resolve gcfree_mesure.

Lemma gcfree_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 gc_free s t -> exists nb : nat, mesure (mk t) nb.

intros s t H gcfree; elim H; clear H.
intros nb H_mes; exists (pred nb); eauto.
Qed.

Hint Resolve gcfree_ex_mesure.

Lemma gcfree1_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> gc_free1 s t -> mesure (mk t) (pred nb).

intros s t nb mes_s gcfree1; inversion mes_s; elim (eq_nat_dec w 0).
intro weqO.
absurd (card_color white (mk s) 0).
elim gcfree1; clear gcfree1.
intros ctls ctlt heap n mksn upd_col; intro cards; inversion cards;
 absurd (mk s n = white); auto.
rewrite <- weqO; assumption.
intro wdifO; replace (pred (g + w)) with (g + pred w).
apply (mesur (mk t)); eauto.
rewrite (plus_pred g w); auto.
Qed.

Hint Resolve gcfree1_mesure.

Lemma gcfree1_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 gc_free1 s t -> exists nb : nat, mesure (mk t) nb.

intros s t H gcfree1; elim H; clear H.
intros nb H_mes; exists (pred nb); eauto.
Qed.

Hint Resolve gcfree1_ex_mesure.


Lemma gcend_mesure :
 forall (s t : state) (nb : nat),
 mesure (mk s) nb -> gc_end s t -> mesure (mk t) nb.

intros s t nb mes_s gcend; elim gcend; clear gcend.
intros ctls ctlt heap mark; rewrite mark; assumption.
Qed.

Hint Resolve gcend_mesure.

Lemma gcend_ex_mesure :
 forall s t : state,
 (exists nb : nat, mesure (mk s) nb) ->
 gc_end s t -> exists nb : nat, mesure (mk t) nb.

intros s t H gcend; elim H; clear H.
intros nb H_mes; exists nb; eauto.
Qed.

Hint Resolve gcend_ex_mesure.


End mesure.

Hint Resolve add_mesure.
Hint Resolve remove_mesure.
Hint Resolve gccall_mesure.
Hint Resolve alloc_mesure.
Hint Resolve marknode_mesure.
Hint Resolve gcstop_mesure.
Hint Resolve gcfree_mesure.
Hint Resolve gcfree1_mesure.
Hint Resolve gcend_mesure.
Hint Immediate add_ex_mesure.
Hint Immediate remove_ex_mesure.
Hint Immediate gccall_ex_mesure.
Hint Immediate alloc_ex_mesure.
Hint Immediate marknode_ex_mesure.
Hint Immediate gcstop_ex_mesure.
Hint Immediate gcfree_ex_mesure.
Hint Immediate gcfree1_ex_mesure.
Hint Immediate gcend_ex_mesure.
Hint Immediate init_ex_mesure.
