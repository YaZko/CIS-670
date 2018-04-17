Section Setoid.

  (** We define predicates over a type of states **)
  Axiom state: Type.
  Definition Pred:= state -> Prop.

  (** We consider extentional equivalence as our equivalence **)
  Definition PEq (P1 P2: Pred): Prop := forall x, P1 x <-> P2 x.
  Infix "≡" := PEq (at level 50).

  (** ≡ is an equivalence relation **)
  Lemma PEq_reflexive: forall P, P ≡ P.
  Proof.
    intros P s; split; auto. 
  Qed.

  Lemma PEq_trans: forall P1 P2 P3 (H1: P1 ≡ P2) (H2: P2 ≡ P3),
      P1 ≡ P3.
  Proof.
    intros P1 P2 P3 H1 H2 s; split; intros H3; [apply H2, H1 | apply H1,H2]; assumption.
  Qed.

  Lemma PEq_symm: forall P1 P2 (H: P1 ≡ P2), P2 ≡ P1.
  Proof.
    intros P1 P2 H s; split; intros H'; apply H; assumption.
  Qed.

  (** However, at this point, we need to use these lemmas explicitly.
      We declare it a parametric relation.
   **)
  Require Import Coq.Setoids.Setoid.

  Add Parametric Relation: Pred PEq
      reflexivity proved by PEq_reflexive
      symmetry proved by PEq_symm
      transitivity proved by PEq_trans
        as PEq_equiv.

  (** Tactics are now supported **)
  Goal forall P, P ≡ P.
    reflexivity.
  Qed.

  (** The underlying mechanism are type classes **)
   Require Import Classes.RelationClasses.

   Instance PEq_equiv': @Equivalence Pred PEq :=
     { Equivalence_Reflexive := PEq_reflexive;
       Equivalence_Symmetric := PEq_symm;
       Equivalence_Transitive := PEq_trans}.
  
  (** The same can be done for weaker relations than equivalence ones.
      Here for an implication for instance
   **)

  Definition PWeaker (P1 P2: Pred): Prop := forall s, P2 s -> P1 s.
  Infix "⊆":= PWeaker (at level 10).
  Lemma PWeaker_reflexive: forall P, P ⊆ P.
  Proof.
    intros ? ?; auto.
  Qed.

  Lemma PWeaker_trans: forall P1 P2 P3 (H1: P1 ⊆ P2) (H2: P2 ⊆ P3), P1 ⊆ P3.
  Proof.
    intros P1 P2 P3 H1 H2 s H3; apply H1,H2,H3.
  Qed.

  Add Parametric Relation: Pred PWeaker
      reflexivity proved by PWeaker_reflexive
      transitivity proved by PWeaker_trans
        as PWeaker_preorder.

  (** We now turn to the question of morphisms **)

  (** We define the join of two predicates, as well as false **)
  Definition PJoin P1 P2: Pred := fun s => P1 s \/ P2 s.
  Infix "∪" := PJoin (at level 15, right associativity).
  Lemma Join_idempotent: forall Q, Q ≡ Q ∪ Q.
  Proof.
    intros Q s; split; intros H.
    left; assumption.
    destruct H; assumption.
  Qed.

  Goal forall Q, Q ≡ Q ∪ Q ∪ Q.
    intros Q.
    (** Fails violently **)
    (* rewrite <- Join_idempotent. *)
  Abort.

  Require Import Setoid.
  
  Add Parametric Morphism : PJoin with
        signature (PEq ==> PEq ==> PEq) as foo.
  Proof.
    intros Q1 Q1' eq1 Q2 Q2' eq2 s; split; intros H;
      (destruct H; [left; apply eq1; assumption | right; apply eq2; assumption]).
  Qed.

  Goal forall Q, Q ≡ Q ∪ Q ∪ Q.
    intros Q.
    do 2 rewrite <- Join_idempotent.
    reflexivity.
  Qed.

  (* Once again, instances can be defined explicitly *)
  Require Import Morphisms.
  Instance foo': Proper (PEq ==> PEq ==> PEq) PJoin.
  Proof.
    intros Q1 Q1' eq1 Q2 Q2' eq2 s; split; intros H;
      (destruct H; [left; apply eq1; assumption | right; apply eq2; assumption]).
  Qed.

  (** For non symmetric relations, we may specify covariant and contravariant morphisms **)
  Definition PImpl (P1 P2: Pred) := fun s => (P1 s -> P2 s).
  Infix "→" := PImpl (at level 15, right associativity).

  Add Parametric Morphism : PImpl with
        signature (PWeaker --> PWeaker ++> PWeaker) as foo''.
  Proof.
    intros Q1 Q1' impl1 Q2 Q2' impl2 s H H1. 
    apply (impl2 s).
    apply H.
    apply (impl1 s).
    assumption.
  Qed.

End Setoid.