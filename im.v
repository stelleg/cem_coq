(* Instruction Machine *)

Require Import assembly util.
Require Import Unicode.Utf8.

Definition Heap := Map Ptr Word.
Definition RegisterFile := Reg → Word.

Inductive State := 
  | st : RegisterFile → Program → Stack → Heap → State.

Definition I (p : Program) : State := st (λ _, 0) p nil nil. 

