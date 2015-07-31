Inductive HeapPtr := | h_ptr : nat -> HeapPtr.
Inductive StackPtr := | s_ptr : nat -> StackPtr.
Inductive InstrPtr := | i_ptr : nat -> InstrPtr.

Inductive Ptr := 
  | ph : HeapPtr -> Ptr
  | ps : StackPtr -> Ptr
  | pl : InstrPtr -> Ptr.

Inductive Word : Type := 
  | wptr : Ptr -> Word
  | wnat : nat -> Word.

Inductive Reg := 
  | IP
  | SP
  | EP 
  | FR
  | R1.

Inductive L : Type :=
  | lreg : Reg -> L
  | lhptr : HeapPtr -> L
  | lsptr : StackPtr -> L.

Inductive R : Type :=
  | rreg : Reg -> R
  | rloc : Reg -> R
  | rword : Word -> R.

Inductive Op : Type :=
  | add : R -> R -> Op.

Inductive Instr : Type :=
  | iset : L -> R -> Instr
  | iop : L -> Op -> Instr.

Inductive Jump : Type :=
  | goto : InstrPtr -> Jump
  | jzero : R -> InstrPtr -> InstrPtr -> Jump.

Definition Heap := HeapPtr -> Word.
Definition Stack := StackPtr -> Word.
Definition Program := InstrPtr -> Instr. 
Definition Registers := Reg -> Word.

Inductive State := 
  | st : Registers -> Program -> Stack -> Heap -> State.

