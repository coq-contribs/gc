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
(*                               lemma_call.v                               *)
(****************************************************************************)

Section lemma_call.

Require Export gc.

Lemma gccall_notaccess_notaccest :
 forall (s t : state) (n : node),
 ~ accessible node (hp s) rt n ->
 gc_call s t -> ~ accessible node (hp t) rt n.

intros s t n notacces_n_s gccall; elim gccall; clear gccall.
intros ctls ctlt heap H_col init; rewrite heap; assumption.
intros ctls ctlt heap grey_node; rewrite heap; assumption.
intros ctls ctlt heap H_col m mksm upd_col; rewrite <- heap; assumption.
Qed.

End lemma_call.