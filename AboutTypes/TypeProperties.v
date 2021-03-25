Require Import List.
Open Scope list_scope.


Section Definitions.
  Variable T : Type.

  Definition Inhabited : Prop := exists e : list T, e <> nil.
  Definition Finite : Prop := exists e : list T, forall t : T, In t e.
End Definitions.

Section Examples_for_Inhabited.
  Example bool_is_Inhabited : Inhabited bool.
  Proof. now exists (true :: nil). Qed.

  Example False_isnot_Inhabited : ~ Inhabited False.
  Proof.
    intro. elim H. intros e H1. apply H1.
    destruct e as [| t e']; [ trivial | now exfalso ].
  Qed.
End Examples_for_Inhabited.

Theorem not_Inhabited_is_Finite : forall T : Type, ~ Inhabited T -> Finite T.
Proof.
  intros* H.
  exists nil. intro. exfalso. apply H.
  exists (t :: nil). intro H'. discriminate H'.
Qed.
