(* Instruction Machine *)
Require Import assembly util relations.
Require Import Unicode.Utf8.
Require Import List.
Import ListNotations.
Require Import util.

Definition Heap := Map Ptr Word.
Definition Stack := list Word.

(*
Definition RegisterFile := Reg → Ptr.
Definition upd (r: Reg) (p: Ptr) (rf: RegisterFile) : RegisterFile := match r with
  | IP => λ r, match r with | IP => p | _ => rf r end
  | EP => λ r, match r with | EP => p | _ => rf r end
  | R1 => λ r, match r with | R1 => p | _ => rf r end
  | R2 => λ r, match r with | R2 => p | _ => rf r end
  | R3 => λ r, match r with | R3 => p | _ => rf r end
  end.
*)

Inductive RegisterFile := mkrf {
  ip : Ptr;
  ep : Ptr;
  r1 : Ptr; 
  r2 : Ptr
}. 

Definition upd (r: Reg) (p: Ptr) (rf: RegisterFile) : RegisterFile := match r,rf with
  | IP, mkrf ip ep r1 r2 => mkrf p ep r1 r2
  | EP, mkrf ip ep r1 r2 => mkrf ip p r1 r2
  | R1, mkrf ip ep r1 r2 => mkrf ip ep p r2
  | R2, mkrf ip ep r1 r2 => mkrf ip ep r1 p
  end.

Definition rff (rf : RegisterFile) (r: Reg) : Ptr := match r with
  | IP => ip rf 
  | EP => ep rf
  | R1 => r1 rf
  | R2 => r2 rf
  end.

Inductive State := st {
  st_rf : RegisterFile;
  st_p : Program;
  st_s : Stack;
  st_h  : Heap
}.

Definition I (p : Program) : State := st (mkrf 1 0 0 0) p nil nil. 

Open Scope nat_scope. 
Inductive read : RO → State → Ptr → Type :=
  | read_reg : ∀ r s, read (RW (WR r)) s (rff (st_rf s) r)
  | read_mem : ∀ r o rf p s h v, 
    lookup (o+rff rf r) h = Some v →
    read (RW (WM r o)) (st rf p s h) v
  | read_const : ∀ c s, read (RC c) s c.

Inductive write : WO → Word → State → State → Type :=
  | write_reg : ∀ r rf p s h w, 
    write (WR r) w (st rf p s h) (st (upd r w rf) p s h)
  | write_mem : ∀ r o rf p s h w, 
    write (WM r o) w (st rf p s h) 
                     (st rf p s (replace beq_nat (o+rff rf r) w h)).

Fixpoint zeroes (n : nat) (p : Ptr) := match n with
  | 0 => []
  | S n => (p, 0)::zeroes n (S p)
  end.

Inductive step_bb : BasicBlock → State → State → Type := 
  | step_push : ∀ rf p s h ro is v sn,
  read ro (st rf p s h) v → 
  step_bb is (st rf p (v::s) h) sn → 
  step_bb (instr (push ro) is) (st rf p s h) sn
  | step_pop : ∀ rf p s h wo is w s' sn,
  write wo w (st rf p s h) s' → 
  step_bb is s' sn →
  step_bb (instr (pop wo) is) (st rf p (w::s) h) sn
  | step_new : ∀ rf p s h wo is w s' n sn,
  (∀ i, i < n → not (In (i+w) (domain h))) →
  w > 0 →
  write wo w (st rf p s (zeroes n w ++ h)) s' →
  step_bb is s' sn → 
  step_bb (instr (new n wo) is) (st rf p s h) sn 
  | step_mov : ∀ s is ro wo s' v sn, 
  read ro s v → write wo v s s' → 
  step_bb is s' sn → 
  step_bb (instr (mov ro wo) is) s sn
  | step_jump0 : ∀ ro k j s s', 
  read ro s 0 →
  write (WR IP) k s s' → 
  step_bb (jump (Some (ro, k)) j) s s'
  | step_jumpS : ∀ ro k j s s' l k', 
  l > 0 →
  read ro s l →
  read j s k → 
  write (WR IP) k s s' → 
  step_bb (jump (Some (ro, k')) j) s s'
  | step_jump : ∀ ro s s' l, 
  read ro s l →
  write (WR IP) l s s' → 
  step_bb (jump None ro) s s'
.

Inductive step : transition State :=
  | enter : ∀ rf p s h k bb sn,
    read IP (st rf p s h) k → 
    nth_error p k = Some bb → 
    step_bb bb (st rf p s h) sn →
    step (st rf p s h) sn.

