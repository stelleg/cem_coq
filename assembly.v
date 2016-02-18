Require Import util.
Require Import Unicode.Utf8.
Require Import expr_db_nat.

Definition Word := nat.
Definition Ptr := nat.
Definition Stack := list Word.

Inductive Reg := 
  | IP
  | EP
  | R1
  | R2
  | R3.

Inductive Op : Type :=
  | word : Word → Op
  | new : Op
  | read : Ptr → Op
  | write : Ptr → Reg → Op
  | sub : Reg → Reg → Op
  | add : Reg → Reg → Op.

Inductive Instr : Type :=
  | op : Reg -> Op -> Instr -> Instr
  | jump : Ptr -> Instr
  | halt : Instr.

Definition Heap := Map Ptr Word.
Definition Program := Map Ptr Instr.
Definition RegisterFile := Reg → Word.

Inductive State := 
  | st : RegisterFile → Program → Stack → Heap → State.

Definition assemble : expr_db_nat.expr → Program.
Admitted. 

