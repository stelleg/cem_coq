Require Import util.
Require Import Unicode.Utf8.

Definition Word := nat.
Definition Ptr := nat.

Inductive Reg := 
  | IP
  | EP
  | R1
  | R2.

Inductive WO := 
  | WR : Reg → WO
  | WM : Reg → nat → WO.

Coercion WR : Reg >-> WO.
Infix "%" := WM (at level 30).

Inductive RO := 
  | RW : WO → RO
  | RC : nat → RO.

Coercion RW : WO >-> RO.
Coercion RC : nat >-> RO.

Inductive Instr : Type :=
  | push : RO → Instr
  | pop : WO → Instr
  | new : nat → WO → Instr 
  | mov : RO → WO → Instr.

Inductive BasicBlock : Type :=
  | instr : Instr → BasicBlock → BasicBlock
  | jump : option (RO*Ptr) → RO → BasicBlock.

Definition Program := list BasicBlock.
