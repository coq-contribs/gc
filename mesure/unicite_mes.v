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
(*                              unicite_mes.v                               *)
(****************************************************************************)

Section unicite_mesure.

Require Export mesure.
Require Export parameters_card.

Lemma measure_unicity :
 forall (nb nb' : nat) (m : marking), mesure m nb -> mesure m nb' -> nb = nb'.

intros nb nb' m H_mes_nb H_mes_nb'; inversion_clear H_mes_nb;
 inversion_clear H_mes_nb'.
cut (g = g0).
cut (w = w0).
intros weqw0 geqg0; auto.
apply unicity_card with (M := m) (P := fun c : color => c = white); auto.
apply unicity_card with (M := m) (P := fun c : color => c = grey); auto.
Qed.

End unicite_mesure.