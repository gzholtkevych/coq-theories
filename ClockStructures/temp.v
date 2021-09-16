Require Import Karazin.ClockStructures.Definitions.
Require Import Karazin.AboutTypes.Examples.
Require Import Coq.Bool.BoolOrder.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Structures.OrdersFacts.

Import RelationClasses.

Definition before_one := fun x y : Event unit => tn unit x < tn unit y.
Definition synchro_one := fun x y : Event unit => tn unit x = tn unit y.
Instance one_clock_struct
: @ClockStruct unit unit_fin before_one synchro_one.
Proof.
  constructor.
  - constructor.
    + compute. intro. destruct x as [_ tx]. intro H.
      induction tx as [| tx' IHtx].
      * inversion H.
      * apply IHtx. now apply le_S_n.
    + compute. intros * H1 H2.
      destruct x as [_ tx]. destruct y as [_ ty]. destruct z as [_ tz].
      assert (H3 : ty <= S ty). { now constructor. }
      assert (H4 : S tx <= S ty). { now constructor. }
      apply Nat.le_trans with (S ty).
Defined.
