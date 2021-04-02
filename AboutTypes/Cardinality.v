Require Import List.

Section Cardinality.
  Variable T : Type.
  Hypothesis eq_dec : forall x y : T, {x = y} + {x <> y}.

  Definition In_dec : forall (x : T) (e : list T), {In x e} + {~ In x e}.
  Proof.
    intros.
    induction e as [| y e' IHe].
    - right. now simpl.
    - pose (eq_decxy := eq_dec x y).
      elim eq_decxy; intro Hxy; elim IHe; intro HIn.
      + left. now right.
      + left. now left.
      + left. now right.
      + right. intro H. elim H; intro H'.
        * now symmetry in H'.
        * contradiction.
  Defined.

  Fixpoint squeeze (lst : list T) : list T :=
    match lst with
      nil => lst
    | x :: nil  => lst
    | x :: lst' => if In_dec x lst' then squeeze lst' else x :: (squeeze lst')
    end.
(*
  Definition card : nat := 
*)


End Cardinality.

Definition eq_dec_nat : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n as [| n' IHn].
  - intro. destruct m; [now left | right; intro H; discriminate H].
  - intro k. case k.
    + right. intro H. discriminate H.
    + intro. elim (IHn n); intro H.
      * left. now rewrite H.
      * right. intro H'. apply H. now injection H'.
Defined.

Compute squeeze nat eq_dec_nat (1 :: 1 :: 2 :: 2 :: 3 :: nil).
