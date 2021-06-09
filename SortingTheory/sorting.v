Inductive cmpout : Set  (* the type inhabited by comparison outcomes *)
  := LT | EQ | GT.

Class Comparable (* the framework for effectively comparable sets *)
  (X : Set) (cmp : X -> X -> cmpout) := {
    EQ_iff_eq : forall x y : X, cmp x y = EQ <-> x = y;
    LT_GT_dual : forall x y : X, cmp x y = LT <-> cmp y x = GT;
    trans : forall x y z : X,
      cmp x y = LT -> cmp y z = LT -> cmp x z = LT
  }.

Definition lt {X : Set} {cmp : X -> X -> cmpout} `{Comparable X cmp}
             (x y : X) : Prop := cmp x y = LT.
Notation "x < y" := (@lt _ _ _ x y).

Definition gt {X : Set} {cmp : X -> X -> cmpout} `{Comparable X cmp}
           (  x y : X) : Prop := cmp x y = GT.
Notation "x > y" := (@gt _ _ _ x y).

Definition leq {X : Set} {cmp : X -> X -> cmpout} `{Comparable X cmp}
               (x y : X) : Prop := x < y \/ x = y.
Notation "x <= y" := (@leq _ _ _ x y).

Section ComparableFacts.
  Variables (X : Set) (cmp : X -> X -> cmpout).
  Context `{HC : Comparable X cmp}.

  Lemma lt_irrefl : forall x : X, ~ lt x x.
  Proof.
    intros * H. unfold "_ < _" in H.
    assert (H' : cmp x x = EQ). { now apply HC. }
    rewrite H' in H. discriminate H.
  Qed.

  Lemma lt_trans : forall x y z : X, x < y -> y < z -> x < z.
  Proof.
    unfold "_ < _". intros * Hxy Hyz.
    now apply trans with y.
  Qed.

  (* Thus, we have obtained "_ < _" is a strict order *)

  Lemma lt_gt_dual : forall x y : X, x < y <-> y > x.
  Proof.
    intros. unfold "_ > _", "_ < _". apply LT_GT_dual.
  Qed.

  Lemma gt_irrefl : forall x : X, ~ x > x.
  Proof.
    intros * H. apply lt_gt_dual in H. revert dependent x.
    exact lt_irrefl.
  Qed.

  Lemma gt_trans : forall x y z : X, x > y -> y > z -> x > z.
  Proof.
    intros * Hxy Hyz. apply lt_gt_dual in Hxy. apply lt_gt_dual in Hyz.
    apply lt_gt_dual. now apply lt_trans with y.
  Qed.

  (* Thus, we have obtained "_ > _" is a strict order *)

  Lemma leq_refl : forall x : X, x <= x.
  Proof.
    intro. unfold "_ <= _". now right.
  Qed.

  Lemma leq_asymm : forall x y : X, x <= y -> y <= x -> x = y.
  Proof.
    intros * Hxy Hyx. elim Hyx; elim Hxy; intros H1 H2; assumption || idtac.
    - exfalso. assert (C : x < x). { now apply lt_trans with y. }
      now apply (lt_irrefl x).
    - now symmetry.
  Qed.

  Lemma leq_trans : forall x y z : X, x <= y -> y <= z -> x <= z.
  Proof.
    intros * Hxy Hyz. elim Hyz; elim Hxy; intros H1 H2.
    - left. now apply lt_trans with y.
    - now rewrite H1.
    - rewrite <- H2. now left.
    - right. now transitivity y.
  Qed.

  (* Thus, we have obtained "_ <= _" is an order *)

End ComparableFacts.

Section SortingProblem.
  Variables (X : Set) (cmp : X -> X -> cmpout).
  Context `{HC : Comparable X cmp}.

End SortingProblem.