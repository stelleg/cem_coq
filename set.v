(* Library for Finite Sets *)
Require Import List Basics.

Definition set := list. 

Fixpoint subset {A} (l : list A) (m: list A) : Prop := match l with
  | nil => True
  | cons x xs => In x m /\ subset xs m
  end.

Definition subset' {A} (l m : list A) : Prop := forall a, In a l -> In a m.


