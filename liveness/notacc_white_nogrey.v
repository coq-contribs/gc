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
(*                          notacc_white_nogrey.v                           *)
(****************************************************************************)

Section notacc_white_nogrey.

Require Export parameters_card.
Require Export lemma_step.
Require Export notfree_notacc.

Notation Step := (step (fun (a : label) (s t : state) => transition s t a))
  (only parsing).
Notation Stream := (stream state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Trace := (trace (fun (a : label) (s t : state) => transition s t a))
  (only parsing).

Definition notacc_white_nogrey (s : state) (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\ mk s n = white /\ card_color grey (mk s) 0.

Definition notacc_white_nogrey_or_free (s : state) 
  (n : node) : Prop :=
  ~ accessible node (hp s) rt n /\ mk s n = white /\ card_color grey (mk s) 0 \/
  mk s n = free.

Lemma add_idem_or_free :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 notacc_white_nogrey s n -> add_edge s t -> notacc_white_nogrey_or_free t n.

intros s t n inv H addedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_grey; left.
split; eauto.
split; eauto.
constructor; inversion H_grey; eauto.
Qed.

Hint Resolve add_idem_or_free.

Lemma remove_idem_or_free :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 notacc_white_nogrey s n ->
 remove_edge s t -> notacc_white_nogrey_or_free t n.

intros s t n inv H removeedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_grey; left.
split; eauto.
split; eauto.
constructor; inversion H_grey; eauto.
Qed.

Hint Resolve remove_idem_or_free.

Lemma alloc_idem_or_free :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 notacc_white_nogrey s n -> alloc s t -> notacc_white_nogrey_or_free t n.

intros s t n inv H addedge; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_grey; left.
split.
apply (alloc_notacces_t s t n);
 [ split; [ rewrite mksn; discriminate | assumption ] | assumption ].
split; eauto.
constructor; inversion H_grey; eauto.
Qed.

Hint Resolve alloc_idem_or_free.

Lemma gccall_idem_or_free :
 forall (s t : state) (n : node),
 notacc_white_nogrey s n -> gc_call s t -> notacc_white_nogrey_or_free t n.

intros s t n H gccall; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_card; elim gccall; clear gccall.
intros ctls ctlt heap H_col H_init; absurd (mk s n = white); auto.
elim (H_col n); intro mksn2; rewrite mksn2; discriminate.
intros ctls ctlt heap H_grey; elim H_grey; clear H_grey.
intros g mksg mktg mark1 mark2; inversion H_card; absurd (mk s g = grey);
 auto.
intros ctls ctlt heap H_col m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; right; rewrite neqm; assumption.
intro ndifm; left; split;
 [ rewrite <- heap; assumption
 | split; [ rewrite <- (mark n ndifm); assumption | constructor; intro n' ] ].
elim (eq_dec_node n' m).
intro n'eqm; intro mktn'; absurd (mk t n' = grey); auto.
rewrite n'eqm; rewrite mktm; discriminate.
intro n'difm; rewrite <- (mark n' n'difm); auto.
Qed.

Hint Resolve gccall_idem_or_free.

Lemma mark_idem_or_free :
 forall (s t : state) (n : node),
 notacc_white_nogrey s n -> mark_node s t -> notacc_white_nogrey_or_free t n.

intros s t n H marknode; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_card; elim marknode; clear marknode.
intros ctls ctlt heap H_grey; elim H_grey; clear H_grey.
intros g mksg mktg mark1 mark2; inversion H_card; absurd (mk s g = grey);
 auto.
Qed.

Hint Resolve mark_idem_or_free.

Lemma gcstop_idem_or_free :
 forall (s t : state) (n : node),
 notacc_white_nogrey s n -> gc_stop s t -> notacc_white_nogrey_or_free t n.

intros s t n H gcstop; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_grey; left.
split; eauto.
split; eauto.
constructor; inversion H_grey; eauto.
Qed.

Hint Resolve gcstop_idem_or_free.

Lemma gcfree_idem_or_free :
 forall (s t : state) (n : node),
 notacc_white_nogrey s n -> gc_free s t -> notacc_white_nogrey_or_free t n.

intros s t n H gcfree; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_card; elim gcfree; clear gcfree.
intros ctls ctlt H_col heap m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; right; rewrite neqm; assumption.
intro ndifm; left; split;
 [ rewrite heap; assumption
 | split; [ rewrite <- (mark n ndifm); assumption | constructor; intro n' ] ].
elim (eq_dec_node n' m).
intro n'eqm; intro mktn'; absurd (mk t n' = grey); auto.
rewrite n'eqm; rewrite mktm; discriminate.
intro n'difm; rewrite <- (mark n' n'difm); auto.
Qed.

Hint Resolve gcfree_idem_or_free.

Lemma gcfree1_idem_or_free :
 forall (s t : state) (n : node),
 sweep_no_greys s ->
 notacc_white_nogrey s n -> gc_free1 s t -> notacc_white_nogrey_or_free t n.

unfold sweep_no_greys in |- *; intros s t n H_sweep H gcfree; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_card; elim gcfree; clear gcfree.
intros ctls ctlt heap m mksm upd_col; elim upd_col; clear upd_col.
intros mark mktm; elim (eq_dec_node n m).
intro neqm; right; rewrite neqm; assumption.
intro ndifm; left; split;
 [ rewrite <- heap; assumption
 | split; [ rewrite <- (mark n ndifm); assumption | constructor; intro n' ] ].
elim (eq_dec_node n' m).
intro n'eqm; intro mktn'; absurd (mk t n' = grey); auto.
rewrite n'eqm; rewrite mktm; discriminate.
intro n'difm; rewrite <- (mark n' n'difm).
apply H_sweep; assumption.
Qed.

Hint Resolve gcfree1_idem_or_free.

Lemma gcend_idem_or_free :
 forall (s t : state) (n : node),
 notacc_white_nogrey s n -> gc_end s t -> notacc_white_nogrey_or_free t n.

intros s t n H gcend; elim H; clear H.
intros notacc_n_s H; elim H; clear H.
intros mksn H_grey; left.
split; eauto.
split; eauto.
constructor; inversion H_grey; eauto.
Qed.

Hint Resolve gcend_idem_or_free.

Lemma step_idem_or_free :
 forall (s t : state) (n : node),
 nogrey_accn_imp_blackn s ->
 sweep_no_greys s ->
 notacc_white_nogrey s n ->
 step (fun (a : label) (s t : state) => transition s t a) s t ->
 notacc_white_nogrey_or_free t n.

intros s t n H_inv H_sweep H_n step; elim step; intro a; case a; intro trans;
 inversion_clear trans; eauto.
Qed.

Hint Resolve step_idem_or_free.

Definition notacc_white_nogrey_formula (n : node) : 
  stream_formula state :=
  state2stream_formula
    (fun s : state =>
     ~ accessible node (hp s) rt n /\
     mk s n = white /\ card_color grey (mk s) 0).

Lemma until_idem_or_free :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color white (mk s) 0)) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_white_nogrey_formula n str ->
 until (fun str => notacc_white_nogrey_formula n str)
   (state2stream_formula (fun s : state => mk s n = free)) str.

intros n str H_trace H_ev H_always_sweep H_always_inv H_n.
generalize H_trace H_always_sweep H_always_inv H_n.
elim H_ev; clear H_n H_ev H_trace H_always_sweep H_always_inv str.
unfold notacc_white_nogrey_formula in |- *;
 unfold state2stream_formula in |- *; simpl in |- *.
intros str H_card H_trace H_always_sweep H_always_inv H_n.
elim H_n; clear H_n.
intros notacc_n_hd H; elim H; clear H.
intros mkhdn H_grey; inversion H_card; absurd (mk (head_str str) n = white);
 auto.
unfold notacc_white_nogrey_formula in |- *;
 unfold state2stream_formula in |- *; simpl in |- *.
intros s str H_ev H_ind H_trace H_always_sweep H_always_inv H_n;
 elim (eq_dec_color (mk s n) free); intro mksn.
constructor 1; auto.
constructor 2; auto.
inversion H_trace; inversion H_always_inv; inversion H_always_sweep.
simpl in H1; inversion H1.
apply H_ind; try assumption.
rewrite <- H11; assumption.
cut (notacc_white_nogrey_or_free (head_str str) n).
unfold notacc_white_nogrey_or_free in |- *;
 unfold state2stream_formula in |- *; simpl in |- *; 
 intro h; elim h; clear h.
intro; apply H_ind; auto.
intro H_n_free; constructor 1; auto.
apply step_idem_or_free with (s := s); auto.
Qed.

Hint Resolve until_idem_or_free.

Lemma white_notacc_nogrey_until_eventually_free :
 forall (n : node) (str : stream state),
 trace (fun (a : label) (s t : state) => transition s t a) str ->
 Eventually
   (state2stream_formula (fun s : state => card_color white (mk s) 0)) str ->
 always (state2stream_formula (fun s : state => sweep_no_greys s)) str ->
 always (state2stream_formula (fun s : state => nogrey_accn_imp_blackn s))
   str ->
 notacc_white_nogrey_formula n str ->
 Eventually (state2stream_formula (fun s : state => mk s n = free)) str.

intros n str H_trace H_always_ev H_always_sweep H_always_inv H_n.
cut
 (until (fun str => notacc_white_nogrey_formula n str)
    (state2stream_formula (fun s : state => mk s n = free)) str); 
 eauto.
intro H_until; elim H_until;
 clear H_n H_always_inv H_always_sweep H_trace H_always_ev H_until.
intros str' H_n; constructor 1; assumption.
intros s str' H_until H_ev.
constructor 2; assumption.
Qed.

Hint Resolve white_notacc_nogrey_until_eventually_free.

End notacc_white_nogrey.

Hint Resolve white_notacc_nogrey_until_eventually_free.