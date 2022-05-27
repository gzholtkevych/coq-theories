Require Import Lists.List.
Require Export Relations.Relation_Definitions.


(* -- Finitary types ---------------------------------------------- *)
Class Finitary (X : Type) : Prop :=
  finitary_cert : exists enum : list X, forall x : X, In x enum.


(* -- Binary relations and properties ----------------------------- *)
Class Reflexive {X : Type} (r : relation X) : Prop :=
  refl_cert : forall x : X, r x x.

Class Symmetric {X : Type} (r : relation X) : Prop :=
  symm_cert : forall x y : X, r x y -> r y x.

Class Asymmetric {X : Type} (r : relation X) : Prop :=
  asym_cert : forall x y : X, r x y -> ~ r y x.

Class Transitive {X : Type} (r : relation X) : Prop :=
  trns_cert : forall x y z : X, r x y -> r y z -> r x z.
