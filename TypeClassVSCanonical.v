(** This example comes from:
    [https://softwarefoundations.cis.upenn.edu/draft/qc-current/Typeclasses.html]
 *)

Require Import String.
Open Scope string_scope.

Require Import QuickChick.Decidability.

Definition bool_to_nat (b : bool) : nat := if b then 0 else 42.

Definition nat_to_string (n : nat) : string :=
  if n < 20 ? then "Pretty small" else "Pretty big".

Class MyMap (A B : Type) : Type :=
  { mymap : A -> B }.

Instance MyMap1 : MyMap bool nat :=
  { mymap := bool_to_nat }.

Instance MyMap2 : MyMap nat string :=
  { mymap := nat_to_string }.

Definition e1 := mymap true.
Compute e1.

Definition e2 := mymap 42.
Compute e2.

Fail Definition e3 : string := mymap false.

Instance MyMap_trans {A B C : Type} `{MyMap A B} `{MyMap B C} : MyMap A C :=
  { mymap a := mymap (mymap a) }.

Definition e3 : string := mymap false.
Compute e3.

(*
Definition e4 : list nat := mymap false.
 *)

(** What happened if we use canonical structures? *)

Reset MyMap.

Module MyMap.
  Record class (T1 T2 : Type) := Class { mymap : T1 -> T2 }.
  Structure type := Pack { obj1 : Type; obj2 : Type; class_of : class obj1 obj2 }.
  Definition op (e : type) : obj1 e -> obj2 e :=
    let 'Pack _ _ (Class the_map) := e in the_map.

  Arguments op {e}.
  Arguments Class {T1} {T2}.
End MyMap.

Canonical Structure MyMap1 : MyMap.type :=
  MyMap.Pack bool nat (MyMap.Class bool_to_nat).

Canonical Structure MyMap2 : MyMap.type :=
  MyMap.Pack nat string (MyMap.Class nat_to_string).

Canonical Structure MyMap_trans (e1 e2 : MyMap.type)
          `{MyMap.obj2 e1 = MyMap.obj1 e2} : MyMap.type.
refine (MyMap.Pack (MyMap.obj1 e1) (MyMap.obj2 e2) (MyMap.Class _)).
intro. apply MyMap.op. rewrite <- H. apply MyMap.op. assumption.
Defined.

Definition e1 := MyMap.op true.
Compute e1.

Definition e2 := MyMap.op 42.
Compute e2.

Definition e3 : string := MyMap.op false.
Compute e3.
