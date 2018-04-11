(** Motivating Example *)

Require Import ssrfun.
Require Import ZArith.

Structure abGrp : Type :=
  AbGrp {
      carrier : Type;
      zero : carrier;
      opp: carrier -> carrier;
      add : carrier -> carrier -> carrier;
      add_assoc : associative add;
      add_comm  : commutative add;
      zero_idl  : left_id zero add;
      add_oppl  : left_inverse zero opp add;
    }.
(* begin hide *)
Arguments zero {_}.
(* end hide *)

Lemma subr0 : forall (aG : abGrp) (x : carrier aG),
    add aG x (opp aG zero) = x.
Proof.
  intros.
  pose proof add_oppl aG zero.
  rewrite add_comm, zero_idl in H.
  rewrite H, add_comm, zero_idl.
  reflexivity.
Qed.
(* begin hide *)
Open Scope Z_scope.
(* end hide *)

Definition Z_abGrp : abGrp :=
  AbGrp Z 0 Z.opp Z.add Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.

Goal forall z, z - 0 = z.
Proof.
  Fail apply subr0.
Abort.

Reset Z_abGrp.

Canonical Structure Z_abGrp : abGrp :=
    AbGrp Z 0 Z.opp Z.add Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.

Goal forall z, z - 0 = z.
Proof.
  apply subr0.
Qed.

Open Scope nat_scope.

Module EQ.
  Record class (T : Type) := Class { cmp : T -> T -> Prop }.
  Arguments Class {T} cmp.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class the_cmp) := e in the_cmp.
  Arguments op {e} x y.

  Module theory.
    Notation "x == y" := (op x y) (at level 70).
  End theory.
End EQ.

Import EQ.theory.
Fail Check 3 == 3.

Definition nat_eq (x y : nat) := nat_compare x y = Eq.
Definition nat_EQcl : EQ.class nat := EQ.Class nat_eq.
Canonical Structure nat_EQty : EQ.type := EQ.Pack nat nat_EQcl.

Check 3 == 3.

Fail Check forall (e : EQ.type) (a b : EQ.obj e), (a, b) == (a, b).

Definition pair_eq (e1 e2 : EQ.type) (x y : EQ.obj e1 * EQ.obj e2) :=
  fst x == fst y /\ snd x == snd y.
Definition pair_EQcl (e1 e2 : EQ.type) := EQ.Class (pair_eq e1 e2).
Canonical Structure pair_EQty (e1 e2 : EQ.type) : EQ.type :=
  EQ.Pack (EQ.obj e1 * EQ.obj e2) (pair_EQcl e1 e2).

Check forall (e : EQ.type) (a b : EQ.obj e), (a, b) == (a, b).

Module LE.
  Record class (T : Type) := Class { cmp : T -> T -> Prop }.
  Arguments Class {T} cmp.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class the_cmp) := e in the_cmp.
  Arguments op {e} x y.

  Module theory.
    Notation "x <= y" := (op x y) (at level 70).
  End theory.
End LE.

Import LE.theory.

Definition nat_LEcl : LE.class nat := LE.Class Nat.le.
Canonical Structure nat_LEty : LE.type := LE.Pack nat nat_LEcl.

Fail Check forall (e : EQ.type) (x y : EQ.obj e), x <= y -> y <= x -> x == y.

Definition pair_le (e1 e2 : LE.type) (x y : LE.obj e1 * LE.obj e2) :=
  fst x <= fst y /\ snd x <= snd y.
Definition pair_LEcl (e1 e2 : LE.type) := LE.Class (pair_le e1 e2).
Canonical Structure pair_LEty (e1 e2 : LE.type) : LE.type :=
  LE.Pack (LE.obj e1 * LE.obj e2) (pair_LEcl e1 e2).

Module LEQ.
  Record mixin (e : EQ.type) (le : EQ.obj e -> EQ.obj e -> Prop) :=
    Mixin { compat : forall (x y : EQ.obj e), (le x y /\ le y x) <-> x == y }.
  Record class T := Class {
    EQ_class : EQ.class T;
    LE_class : LE.class T;
    extra : mixin (EQ.Pack T EQ_class) (LE.cmp T LE_class) }.
  Structure type := _Pack { obj : Type; class_of : class obj }.
  Arguments Mixin {e le} _.
  Arguments Class {T} _ _ _.

  Module theory.
    Fail Check forall (leq : type) (n m : obj leq),
        n <= m -> m <= n -> n == m.

    Definition to_EQ (leq : type) : EQ.type :=
      EQ.Pack (obj leq) (EQ_class _ (class_of leq)).
    Definition to_LE (leq : type) : LE.type :=
      LE.Pack (obj leq) (LE_class _ (class_of leq)).
    Canonical Structure to_EQ.
    Canonical Structure to_LE.

    Check forall (leq : type) (n m : obj leq),
        n <= m -> m <= n -> n == m.

    Lemma lele_eq (leq : type) (x y : obj leq) :
      x <= y -> y <= x -> x == y.
    Proof. intros; apply (compat _ _ (extra _ (class_of leq))); intuition. Qed.

    Arguments lele_eq {leq} x y _ _.
  End theory.
End LEQ.

Import LEQ.theory.

Lemma nat_LEQ_compat (n m : nat) : n <= m /\ m <= n <-> n == m.
Proof.
  split.
  - intros. destruct H. apply (Nat.le_antisymm _ _ H) in H0.
    apply Nat.compare_eq_iff. assumption.
  - intros. apply Nat.compare_eq_iff in H. rewrite H.
    split; apply Nat.le_refl.
Qed.
Definition nat_LEQmx := LEQ.Mixin nat_LEQ_compat.
Canonical Structure nat_LEQty : LEQ.type :=
  LEQ._Pack nat (LEQ.Class nat_EQcl nat_LEcl nat_LEQmx).

Goal forall (n m : nat), n <= m -> m <= n -> n == m.
Proof.
  intros n m.
  Fail apply lele_eq.
  apply (lele_eq n m).
Qed.

Lemma pair_LEQ_compat (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
  (n <= m /\ m <= n) <-> n == m.
Proof.
  destruct n as [a b]; destruct m as [c d]. split.
  - intros. destruct H as [H1 H2].
    inversion H1. inversion H2. constructor.
    + apply (LEQ.compat _ _ (LEQ.extra _ (LEQ.class_of l1)));
        split; assumption.
    + apply (LEQ.compat _ _ (LEQ.extra _ (LEQ.class_of l2)));
        split; assumption.
  - intros. inversion H as [H1 H2].
    apply (LEQ.compat _ _ (LEQ.extra _ (LEQ.class_of l1))) in H1.
    apply (LEQ.compat _ _ (LEQ.extra _ (LEQ.class_of l2))) in H2.
    split; constructor; intuition.
Qed.

Definition pair_LEQmx (l1 l2 : LEQ.type) :=
  LEQ.Mixin (pair_LEQ_compat l1 l2).

Canonical Structure pair_LEQty (l1 l2 : LEQ.type) : LEQ.type :=
  LEQ._Pack (LEQ.obj l1 * LEQ.obj l2)
            (LEQ.Class
               (pair_EQcl (to_EQ l1) (to_EQ l2))
               (pair_LEcl (to_LE l1) (to_LE l2))
               (pair_LEQmx l1 l2)).

Goal forall (n m : (nat * nat) * nat), n <= m -> m <= n -> n == m.
Proof. intros n m. apply (lele_eq n m). Qed.
