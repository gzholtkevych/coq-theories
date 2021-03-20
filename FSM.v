Require Import Karazin.TypeProperties.
Require Import List.
Open Scope list_scope.


Class FSM (X Z : Set)
          (f : Z -> X -> Z) := {
  input := X; state := Z; do := f;
  fin_input : Finite input;
  fin_state : Finite state;
  run : state -> list input -> state := fix h s u :=
    match u with
      nil     => s
    | a :: u' => do (h s u') a
    end
}.

Inductive off_on : Set := off : off_on | on : off_on.
Inductive set_reset : Set := set : set_reset | reset : set_reset.
Definition switch (z : off_on) (x : set_reset) : off_on :=
  match z, x with
    off, reset => off
  | off, set   => on
  | on, reset  => off
  | on, set    => on
  end.

Instance switcher : FSM set_reset off_on switch.
Proof.
  split; exists (set :: reset :: nil) || exists (on :: off :: nil);
  intro; destruct t; (left; reflexivity) || (right; left); reflexivity. 
Defined.


Class FSA {X Z : Set} {f : Z -> X -> Z} `{FSM X Z f}
      (z0 : Z) (g : Z -> bool) := {
  init := z0;
  decision := g;
  accept : list input -> bool := fun u => decision (run init u)
}.

Definition ok_on (s : off_on) : bool :=
  match s with
    off => false
  | on => true
  end.

Definition ok_off (s : off_on) : bool :=
  match s with
    off => true
  | on => false
  end.

Instance on_acceptor : FSA off ok_on.
Proof. split. Defined.

Instance off_acceptor : FSA off ok_off.
Proof. split. Defined.

Existing Instance on_acceptor.
Example ex_1 :
  accept (set :: reset :: set :: set :: nil) = true.
Proof. now compute. Qed.

Existing Instance off_acceptor.
Example ex_2 :
  accept (set :: reset :: set :: set :: nil) = false.
Proof. now compute. Qed.

Class FST (X Y Z : Set) (z0 : Z) (f : Z -> X -> Z)
  (g : Z -> X -> Y) `{FSM X Z z0 f} : Type := {
  output := Y; show := g;
  fin_out : Finite output;
  behaviour : list input -> list output :=
    fix f u := match u with
                 nil => nil
               | a :: u' => (show (run init u') a) :: (f u')
    end
}.

Section FSM_Examples.
  Inductive off_on : Set := off : off_on | on : off_on.
  Inductive set_reset : Set := set : set_reset | reset : set_reset.

  Lemma fin_set_reset : Finite set_reset.
  Proof.
    exists (set :: reset :: nil). intro.
    destruct t; simpl.
    - now left.
    - right. now left.
  Qed.

  Lemma fin_off_on : Finite off_on.
  Proof.
    exists (off :: on :: nil). intro.
    destruct t; simpl.
    - now left.
    - right. now left.
  Qed.

  Definition f (z : off_on) (x : set_reset) : off_on :=
    match z, x with
      off, reset => off
    | off, set   => on
    | on, reset  => off
    | on, set    => on
    end.

  Instance m : FSM set_reset off_on off f := {|
    fin_input := fin_set_reset; fin_state := fin_off_on
  |}.

  Definition g (s : off_on) : bool :=
    match s with off => false | on  => true end.

  Instance ma : FSA set_reset off_on off f g := {}.
  Proof. constructor.
End FSM_Examples.

Section FST_Example.
  Inductive A : Set := green : A | red : A.
  Inductive B : Set := even : B | odd : B.
  Inductive S : Set := init : S | another : S.
  Let f (s : S) (a : A) : S * B :=
    match s with
      init => match a with
                red => (init, even)
              | green => (another, odd)
              end
    | another => match a with
                   red => (another, odd)
                 | green => (init, even)
                 end
    end.
  Lemma finABS : Finite A /\ Finite B /\ Finite S.
  Proof.
    repeat split; [
      exists (green :: red :: nil)
    | exists (even :: odd :: nil)
    | exists (init :: another :: nil)]; intro;
    destruct t; (now left) || (right; now left).
  Qed.

  Let m : FST := {|
    input := A; output := B; state := S; do := f;
    fin := finABS
  |}.
End FST_Example.














































































































