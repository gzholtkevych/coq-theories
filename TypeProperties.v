Require Import List.
Open Scope list_scope.
Require Import Arith.PeanoNat.
Open Scope nat_scope.


Section Definitions.
  Variable T : Type.

  Definition Inhabited : Prop := exists e : list T, e <> nil.
  Definition Finite : Prop := exists e : list T, forall t : T, In t e.
End Definitions.

Example bool_is_Inhabited : Inhabited bool.
Proof. now exists (true :: nil). Qed.

Example False_isnot_Inhabited : ~ Inhabited False.
Proof.
  intro. elim H. intros e H1. apply H1.
  destruct e as [| t e']; [ trivial | now exfalso ].
Qed.

Example False_is_Finite : Finite False.
Proof. now exists nil. Qed.

Theorem not_Inhabited_is_Finite : forall T : Type, ~ Inhabited T -> Finite T.
Proof.
  intros* H.
  exists nil. intro. exfalso. apply H.
  exists (t :: nil). intro H'. discriminate H'.
Qed.

Example bool_is_Finite : Finite bool.
Proof.
  exists (true :: false :: nil). intro.
  destruct t; [ now left | right; now left ].
Qed.

Theorem nat_isnot_Finite : ~ Finite nat.
(*  The idea of the proof is to construct a function outside : list nat -> nat
    meeting the requirement
      forall e : list nat, ~ In (outside e) e.                                *)
Admitted.
