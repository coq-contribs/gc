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
(*                               parameters.v                               *)
(****************************************************************************)

Section parameters.

Parameter node : Set.

Parameter rt : node.

Axiom eq_dec_node : forall n m : node, {n = m} + {n <> m}.

Definition heap := node -> node -> bool.

Inductive color : Set :=
  | white : color
  | black : color
  | grey : color
  | free : color.

Lemma eq_dec_color : forall c1 c2 : color, {c1 = c2} + {c1 <> c2}.
intros c1 c2.
case c1; case c2; (right; discriminate) || (left; reflexivity).
Qed.

Definition marking := node -> color.

Lemma noteqmar_noteqnod :
 forall (m1 : marking) (n m : node), m1 n <> m1 m -> n <> m.

unfold not in |- *; intros m1 n m m1ndifm1m neqm; apply m1ndifm1m;
 rewrite neqm; trivial.
Qed.


Inductive control : Set :=
  | mutate : control
  | mark : control
  | sweep : control.

Record state : Set := c_state {hp : heap; mk : marking; ctl : control}.

End parameters.