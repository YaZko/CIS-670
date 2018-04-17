Require Arith.

(** * Basic setup *)

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

Instance Nat_Preord : Preord nat :=
  { ord x y := x <= y }.
- reflexivity.
- etransitivity; eassumption.
Qed.

Instance Preord_Eq (T : Type) { H: Preord T} : Eq T :=
  { eq x y := x ≤ y /\ y ≤ x }.
- intros. destruct H. split; apply ord_refl0.
- intuition.
- intros. destruct H0; destruct H1; destruct H.
  split; eapply ord_trans0; eauto.
Qed.

(** * A naive approach *)

Require Import Streams.

CoInductive stream_ub {T : Type} `{Preord T} : Stream T -> T -> Prop :=
| stream_hd_lt : forall h t x,
    h ≤ x -> stream_ub t x -> stream_ub (Cons h t) x.

Class CPO (T : Type) `{Preord T} :=
  { lub : (Stream T) -> T;
    le_lub : forall (c : Stream T), stream_ub c (lub c);
    lub_le : forall (c : Stream T) x, stream_ub c x -> lub c ≤ x
  }.

Definition flat := option.

Inductive flat_ord {A : Type} : flat A -> flat A -> Prop :=
| flatNone : forall x, flat_ord None x
| flatSome : forall a, flat_ord (Some a) (Some a).

Instance Flat_Preord (A : Type) : Preord (flat A) :=
  { ord := flat_ord }.
- destruct x; constructor.
- inversion 1; inversion 1; subst; constructor.
Qed.

Definition flat_lub {A : Type} (c : Stream (flat A)) : flat A.
Abort.

Reset stream_ub.

(** * A different representation of chains *)

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

Class CPO (T : Type) `{Preord T} :=
  { lub : (Hom nat T) -> T;
    le_lub : forall (c : Hom nat T) n, c n ≤ lub c;
    lub_le : forall (c : Hom nat T) x, (forall n, c n ≤ x) -> lub c ≤ x
  }.

(** Recall a flat domain is a domain with a bottom elements ⊥.
    a ≤ b if and only if either a = ⊥ or a = b. *)

Definition flat := option.

Inductive flat_ord {A : Type} : flat A -> flat A -> Prop :=
| flatNone : forall x, flat_ord None x
| flatSome : forall a, flat_ord (Some a) (Some a).

Instance Flat_Preord (A : Type) : Preord (flat A) :=
  { ord := flat_ord }.
- destruct x; constructor.
- inversion 1; inversion 1; subst; constructor.
Qed.

Definition flat_lub {A : Type} (c : Hom nat (flat A)) : flat A.
Abort.

Reset flat.

(** * The Paulin-Mohring approach

    See: Christine Paulin-Mohring. A constructive denotational
    semantics for Kahn networks in Coq. From Semantics to Computer
    Science, Cambridge University Press, pp.383-413, 2009,
    9780521518253. *)

CoInductive flat (A : Type) :=
| Eps : flat A -> flat A
| Val : A -> flat A.

Arguments Eps {_}.
Arguments Val {_}.

Fixpoint idx {A : Type} (f : flat A) (n : nat) : flat A :=
  match f with
  | Val a => Val a
  | Eps x =>
    match n with
    | O => Eps x
    | S n' => idx x n'
    end
  end.

CoInductive flat_ord {A : Type} : flat A -> flat A -> Prop :=
| flatEps  : forall x y, flat_ord x y -> flat_ord (Eps x) (Eps y)
| flatValR : forall x a, flat_ord x (Val a) -> flat_ord (Eps x) (Val a)
| flatValL : forall a y n, idx y n = Val a -> flat_ord (Val a) y.

Lemma ord_idx : forall {A : Type} n (x y : flat A) a,
    idx x n = Val a ->
    flat_ord x y ->
    exists m, idx y m = Val a.
Proof.
  induction n.
  - intros. inversion H0; subst.
    + simpl in H; discriminate.
    + simpl in H; discriminate.
    + simpl in H; inversion H; subst. exists n. assumption.
  - intros. inversion H0; subst.
    + simpl in H. apply (IHn _ _ _ H) in H1.
      destruct H1 as [m ?]. exists (S m). simpl; assumption.
    + simpl in H. apply (IHn _ _ _ H) in H1. assumption.
    + simpl in H; inversion H; subst. exists n0. assumption.
Qed.

Instance Flat_Preord (A : Type) : Preord (flat A) :=
  { ord := flat_ord }.
- cofix. destruct x.
  + apply flatEps. apply Flat_Preord.
  + apply flatValL with (n:=0). reflexivity.
- cofix. inversion 2; subst.
  + inversion H; subst.
    * constructor. eauto.
    * apply (ord_idx _ _ _ _ H2) in H0.
      destruct H0 as [m ?]. apply flatValL with (n0:=m). assumption.
  + inversion H; subst.
    * constructor; eauto.
    * apply (ord_idx _ _ _ _ H2) in H0.
      destruct H0 as [m ?]. apply flatValL with (n0:=m). assumption.
  + generalize dependent x.
    generalize dependent z. induction n; intros.
    * simpl in H1. destruct z; try discriminate.
      inversion H1; subst. assumption.
    * simpl in H1. destruct z.
      -- destruct x.
         ++ constructor. apply IHn; auto.
            ** inversion H0; subst.
               destruct n0; simpl in H3; try discriminate.
               econstructor; eassumption.
            ** inversion H; assumption.
         ++ inversion H; subst.
            destruct n0; simpl in H3; inversion H3; subst; assumption.
      -- inversion H1; subst. assumption.
Qed.

CoFixpoint flat_lub {A : Type} (c : Hom nat (flat A)) (m n : nat) : flat A :=
  match idx (c m) n with
  | Val a => Val a
  | Eps _ =>
    match m with
    | O => Eps (flat_lub c (n + 1) (n + 1))
    | S n' => Eps (flat_lub c (m - 1) n)
    end
  end.

Instance Flat_CPO (A : Type) : CPO (flat A) :=
  { lub c := flat_lub c 0 0 }.
Admitted.
