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
(*                            parameters_card.v                             *)
(****************************************************************************)

Section parameters_card.

Require Export gc.
Require Export card.

Notation Card := (card _ _) (only parsing).

Inductive grey_white_sons (m1 m2 : marking) (h1 h2 : heap) 
(g : node) : Prop :=
    grey_sons :
      (forall n m : node, h1 n m = h2 n m) ->
      (forall m : node, h1 g m = true /\ m1 m = white -> m2 m = grey) ->
      (forall m : node,
       m <> g /\ (h1 g m = true /\ m1 m <> white \/ h1 g m = false) ->
       m1 m = m2 m) -> grey_white_sons m1 m2 h1 h2 g. 

Definition card_color (c0 : color) :=
  card node color (fun c : color => c = c0).

Inductive card_sons (n0 : node) (c0 : color) (m : marking) 
(h : heap) (nb : nat) : Prop :=
    CS :
      forall M : node -> bool * color,
      (forall n : node, M n = (h n0 n, m n)) ->
      card _ _
        (fun p : bool * color =>
         match p with
         | (b, c) => b = true /\ c = c0
         end) M nb -> card_sons n0 c0 m h nb.

Definition update_heap (b : bool) (h : heap) (n0 f n m : node) :=
  match eq_dec_node n n0 with
  | right _ => h n m
  | left _ =>
      match eq_dec_node m f with
      | right _ => h n0 m
      | left _ => b
      end
  end.
                                          
Lemma exist_updated_heap :
 forall (b : bool) (h : heap) (n0 f : node),
 exists h' : heap,
   (forall n m : node, n <> n0 -> h n m = h' n m) /\
   (forall n : node, n <> f -> h n0 n = h' n0 n) /\ h' n0 f = b.

intros b h n0 f.
split with (update_heap b h n0 f).
unfold update_heap in |- *; split.
intros n m ndifn0.
case (eq_dec_node n n0); auto.
intro neqn0; absurd (n = n0); auto.
split.
intros n ndiff; case (eq_dec_node n0 n0); auto.
intro n0eqn0; case (eq_dec_node n f); auto.
intro neqf; absurd (n = f); auto.
case (eq_dec_node n0 n0); auto.
intro n0eqn0; case (eq_dec_node f f); auto.
intro fdiff; absurd (f = f); auto.
intro n0difn0; absurd (n0 = n0); auto.
Qed.


Lemma not_true_and_white :
 forall (M : node -> bool * color) (m : marking) (h : heap) (n n0 : node),
 (forall n : node, M n = (h n0 n, m n)) ->
 (forall n : node, ~ (let (b0, c0) := M n in b0 = true /\ c0 = white)) ->
 ~ (h n0 n = true /\ m n = white).

intros M m h n n0 Mn H_M.
intro H; elim H; clear H.
intros hn0n mn.
absurd (h n0 n = true /\ m n = white); auto.
elim (H_M n); generalize (refl_equal (M n)); pattern (M n) at -1 in |- *;
 case (M n); intros b c M_n; split.
replace b with (fst (M n)).
rewrite (Mn n); assumption.
rewrite M_n; auto.
replace c with (snd (M n)); auto.
rewrite (Mn n); assumption.
rewrite M_n; auto.
Qed.


Lemma is_white :
 forall (M : node -> bool * color) (h : heap) (m : marking) (n n0 : node),
 (forall n : node, M n = (h n0 n, m n)) ->
 (let (b0, c0) := M n in b0 = true /\ c0 = white) -> m n = white.

intros M h m n n0 Mn H_M.
cut (let (b0, c0) := M n in b0 = true /\ c0 = white); auto.
generalize (refl_equal (M n)); pattern (M n) at -1 in |- *; case (M n);
 intros b c M_n H_b_c; elim H_b_c; clear H_b_c.
intros H_b H_c; replace (m n) with c.
assumption.
replace c with (snd (M n)).
rewrite (Mn n); auto.
rewrite M_n; auto.
Qed.


Lemma is_true :
 forall (M : node -> bool * color) (h : heap) (m : marking) (n n0 : node),
 (forall n : node, M n = (h n0 n, m n)) ->
 (let (b0, c0) := M n in b0 = true /\ c0 = white) -> h n0 n = true.

intros M h m n n0 Mn H_M.
cut (let (b0, c0) := M n in b0 = true /\ c0 = white); auto.
generalize (refl_equal (M n)); pattern (M n) at -1 in |- *; case (M n);
 intros b c M_n H_b_c; elim H_b_c; clear H_b_c.
intros H_b H_c; replace (h n0 n) with b.
assumption.
replace b with (fst (M n)).
rewrite (Mn n); auto.
rewrite M_n; auto.
Qed.


End parameters_card.