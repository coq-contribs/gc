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
(*                               gc.v                                       *)
(****************************************************************************)

Section specification.

Require Export parameters.
Require Export LTL.
Require Export reachable.

Notation State_formula := (state_formula state) (only parsing).

Definition add (h1 h2 : heap) (n0 m0 : node) : Prop :=
  (forall n n1 : node, n <> n0 -> h1 n n1 = h2 n n1) /\
  (forall m : node, m <> m0 -> h1 n0 m = h2 n0 m) /\ h2 n0 m0 = true.

Definition remove (h1 h2 : heap) (n0 m0 : node) : Prop :=
  (forall n n1 : node, n <> n0 -> h1 n n1 = h2 n n1) /\
  (forall m : node, m <> m0 -> h1 n0 m = h2 n0 m) /\ h2 n0 m0 = false.

Definition update_color (m1 m2 : marking) (c : color) 
  (n0 : node) : Prop :=
  (forall n : node, n <> n0 -> m1 n = m2 n) /\ m2 n0 = c.

Definition init_color (m1 m2 : marking) : Prop :=
  m2 rt = grey /\
  (forall n : node, n <> rt -> m1 n = black -> m2 n = white) /\
  (forall n : node, n <> rt -> m1 n <> black -> m2 n = m1 n).


Definition marking_add (m1 m2 : marking) (n m : node) : Prop :=
  m1 n <> black /\ m2 = m1 \/
  m1 n = black /\ m1 m <> white /\ m2 = m1 \/
  m1 n = black /\ m1 m = white /\ update_color m1 m2 grey m.

Lemma cases_marknode :
 forall (m : marking) (h : heap) (n g : node),
 n = g \/
 n <> g /\
 ((h g n = true /\ m n = white \/ h g n = true /\ m n <> white) \/
  h g n = false).

intros m h n g; elim (eq_dec_node n g).
intro neqg; left; assumption.
intro ndifg; right; split; auto.
case (h g n); elim (eq_dec_color (m n) white); intro mn.
left; left; auto.
left; right; auto.
right; trivial.
right; trivial.
Qed.

           
Inductive add_edge (s t : state) : Prop :=
    add_to_node :
      forall n n' : node,
      accessible node (hp s) rt n ->
      accessible node (hp s) rt n' ->
      ctl s = mutate ->
      ctl t = mutate ->
      add (hp s) (hp t) n n' ->
      marking_add (mk s) (mk t) n n' -> add_edge s t.

           
Inductive remove_edge (s t : state) : Prop :=
    remove_to_node :
      forall n n' : node,
      accessible node (hp s) rt n ->
      accessible node (hp s) rt n' ->
      ctl s = mutate ->
      ctl t = mutate ->
      remove (hp s) (hp t) n n' -> mk t = mk s -> remove_edge s t.
                                                                             
Inductive alloc (s t : state) : Prop :=
    alloc_add_free_to_rt :
      ctl s = mutate ->
      ctl t = mutate ->
      forall n : node,
      mk s n = free ->
      (forall fils : node, hp s n fils = true -> remove (hp s) (hp t) n fils) ->
      update_color (mk s) (mk t) black n ->
      add (hp s) (hp t) rt n -> alloc s t. 


Inductive grey_node_case (m1 m2 : marking) (h : heap) : Prop :=
    grey_node :
      forall g : node,
      m1 g = grey ->
      m2 g = black ->
      (forall m : node, h g m = true /\ m1 m = white -> m2 m = grey) ->
      (forall m : node,
       m <> g /\ (h g m = true /\ m1 m <> white \/ h g m = false) ->
       m1 m = m2 m) -> grey_node_case m1 m2 h. 


Inductive gc_call (s t : state) : Prop :=
  | call_gc :
      ctl s = mutate ->
      ctl t = mark ->
      hp t = hp s ->
      (forall n : node, mk s n = black \/ mk s n = free) ->
      init_color (mk s) (mk t) -> gc_call s t
  | call_exist_grey :
      ctl s = mutate ->
      ctl t = mark ->
      hp t = hp s -> grey_node_case (mk s) (mk t) (hp s) -> gc_call s t
  | init_no_greys_but_white :
      ctl s = mutate ->
      ctl t = mark ->
      hp s = hp t ->
      (forall n : node, mk s n <> grey) ->
      forall m : node,
      mk s m = white -> update_color (mk s) (mk t) free m -> gc_call s t.


Inductive mark_node (s t : state) : Prop :=
    mn_exist_grey :
      ctl s = mark ->
      ctl t = mark ->
      hp s = hp t -> grey_node_case (mk s) (mk t) (hp s) -> mark_node s t.


Inductive gc_stop (s t : state) : Prop :=
    gcstop :
      ctl s = mark ->
      ctl t = mutate -> hp t = hp s -> mk t = mk s -> gc_stop s t.

Inductive gc_free (s t : state) : Prop :=
    free_no_grey_but_white :
      ctl s = mark ->
      ctl t = sweep ->
      (forall n : node, mk s n <> grey) ->
      hp t = hp s ->
      forall m : node,
      mk s m = white -> update_color (mk s) (mk t) free m -> gc_free s t.

Inductive gc_free1 (s t : state) : Prop :=
    free1_white :
      ctl s = sweep ->
      ctl t = sweep ->
      hp s = hp t ->
      forall n : node,
      mk s n = white -> update_color (mk s) (mk t) free n -> gc_free1 s t.
                              
Inductive gc_end (s t : state) : Prop :=
    gcend :
      ctl s = sweep ->
      ctl t = mutate -> hp t = hp s -> mk t = mk s -> gc_end s t.

Inductive label : Set :=
  | label_add : label
  | label_rem : label
  | label_alloc : label
  | label_call : label
  | label_mark : label
  | label_stop : label
  | label_free : label
  | label_free1 : label
  | label_end : label.

Inductive transition (s t : state) : label -> Prop :=
  | ae : add_edge s t -> transition s t label_add
  | re : remove_edge s t -> transition s t label_rem
  | al : alloc s t -> transition s t label_alloc
  | gcc : gc_call s t -> transition s t label_call
  | mar : mark_node s t -> transition s t label_mark
  | gcs : gc_stop s t -> transition s t label_stop
  | gcf : gc_free s t -> transition s t label_free
  | gcfr : gc_free1 s t -> transition s t label_free1
  | gce : gc_end s t -> transition s t label_end.
 

Definition fair (a : label) : Prop :=
  match a with
  | label_add => False
  | label_rem => False
  | label_alloc => False
  | label_call => True
  | label_mark => True
  | label_stop => False
  | label_free => True
  | label_free1 => True
  | label_end => False
  end.

Definition init_marking (m : marking) : Prop :=
  m rt = black /\ (forall n : node, n <> rt -> m n = free).

Definition init_state : state_formula state :=
  fun s =>
  ctl s = mutate /\
  init_marking (mk s) /\ (forall n1 n2 : node, hp s n1 n2 = false).

Definition rt_grey_or_black : state_formula state :=
  fun s => mk s rt = grey \/ mk s rt = black.

Definition no_edge_black_to_white : state_formula state :=
  fun s =>
  forall n : node,
  mk s n = black -> forall m : node, mk s m = white -> hp s n m = false.

Definition no_edge_black_to_white_bis : state_formula state :=
  fun s =>
  forall n m : node, mk s n = black -> hp s n m = true -> mk s m <> white.

Definition nogrey_accn_imp_blackn : state_formula state :=
  fun s =>
  (forall n1 : node, mk s n1 <> grey) ->
  forall n2 : node, accessible node (hp s) rt n2 -> mk s n2 = black.

Definition sweep_no_greys : state_formula state :=
  fun s => ctl s = sweep -> forall n : node, mk s n <> grey.

Definition acc_imp_notfree : state_formula state :=
  fun s => forall n : node, accessible node (hp s) rt n -> mk s n <> free.



End specification.
