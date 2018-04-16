Require Arith.

Class Eq (T : Type) :=
  { eq : T -> T -> Prop;
    eq_refl : forall x, eq x x;
    eq_symm : forall x y, eq x y -> eq y x;
    eq_trans : forall x y z, eq x y -> eq y z -> eq x z }.

Notation "x == y" := (eq x y) (at level 42).

Class Preord (T : Type) :=
  { ord : T -> T -> Prop;
    ord_refl : forall x, ord x x;
    ord_trans : forall x y z, ord x y -> ord y z -> ord x z }.

Notation "x ≤ y" := (ord x y) (at level 42).

Instance PreordNat : Preord nat :=
  { ord x y := x <= y }.
- reflexivity.
- etransitivity; eassumption.
Qed.

Check (1 ≤ 1).

Instance Preord_Eq (T : Type) `{Preord T} : Eq T :=
  { eq x y := x ≤ y /\ y ≤ x }.
- intros. destruct H. split; apply ord_refl0.
- intuition.
- intros. destruct H0; destruct H1; destruct H.
  split; eapply ord_trans0; eauto.
Qed.

Set Typeclasses Debug.

Check (1 == 1).

Class Hom (A B : Type) `{Preord A} `{Preord B} :=
  { map : A -> B;
    map_axiom : forall (x y : A),
        x ≤ y -> map x ≤ map y }.

Arguments map {A} {B} {_} {_}.
Coercion map : Hom >-> Funclass.

Instance Hom_Preord (A B : Type) `{Preord A} `{Preord B} : Preord (Hom A B) :=
  { ord x y := forall a, x a ≤ y a }.
- intros. destruct H0. apply ord_refl0.
- intros. destruct H0. eapply ord_trans0. apply H1. apply H2.
Qed.

Check (forall (f : Hom (Hom nat nat) (Hom nat nat)), f == f).

Reset Eq.

Module Eq.
  Record mixin_of (T : Type) :=
    Mixin {
        op : T -> T -> Prop;
        refl : forall x, op x x;
        symm : forall x y, op x y -> op y x;
        trans : forall x y z, op x y -> op y z -> op x z
      }.

  Structure type :=
    Pack { sort :> Type; mixin : mixin_of sort }.

  Definition eq_op (t : type) := op _ (mixin t).
  
  Module Notations.
    Notation "x == y" := (eq_op _ x y) (at level 42).
  End Notations.
End Eq.

Import Eq.Notations.

Fail Check (1 == 1).

Module Preord.
  Record mixin_of (T : Type) :=
    Mixin {
        op : T -> T -> Prop;
        refl : forall x, op x x;
        trans : forall x y z, op x y -> op y z -> op x z }.

  Structure type :=
    Pack { sort :> Type; mixin : mixin_of sort }.

  Definition ord_op (t : type) := op _ (mixin t).

  Module Notations.
    Notation "x ≤ y" := (ord_op _ x y) (at level 42).
  End Notations.
End Preord.

Import Preord.Notations.

Fail Check (1 ≤ 1).

Definition nat_ord_op x y := x <= y.

Lemma nat_ord_refl : forall (x : nat), x <= x.
Proof. reflexivity. Qed.

Lemma nat_ord_trans : forall (x y z : nat),
    x <= y -> y <= z -> x <= z.
Proof. etransitivity; eassumption. Qed.

Definition Preord_mixin_of_nat : Preord.mixin_of nat :=
  Preord.Mixin _ nat_ord_op nat_ord_refl nat_ord_trans.

Coercion Eq.sort : Eq.type >-> Sortclass.
Coercion Preord.sort : Preord.type >-> Sortclass.

Canonical Structure nat_preordTy : Preord.type :=
  Preord.Pack nat Preord_mixin_of_nat.

Definition eq_op (t : Preord.type) (x y : t) :=
  x ≤ y /\ y ≤ x.

Definition Eq_mixin_of_perord (t : Preord.type) : Eq.mixin_of t.
  refine (Eq.Mixin _ (eq_op t) _ _ _).
  - intros. destruct t; destruct mixin. split; apply refl.
  - unfold eq_op. intuition.
  - intros. destruct H; destruct H0; destruct t; destruct mixin.
    split; eapply trans; eauto.
Qed.

Canonical Structure preord_eqTy (t : Preord.type) : Eq.type :=
  Eq.Pack t (Eq_mixin_of_perord t).

Set Printing All.
Check (1 ≤ 1).

Check (1 == 1).

