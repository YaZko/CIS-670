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
