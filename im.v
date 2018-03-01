(* Instruction Machine *)

Require Import assembly util relations.
Require Import Unicode.Utf8.
Require Import List.
Import ListNotations.
Require Import util.

Definition Heap := Map Ptr Word.
Definition Stack := list Word.
Definition RegisterFile := Reg → Ptr.

(*
Inductive RegisterFile := rf {
  ip : Ptr;
  ep : Ptr;
  r1 : Ptr; 
  r2 : Ptr;
  r3 : Ptr
}. 

Definition rff (r: Reg) : RegisterFile → Ptr := match r with
  | IP => ip 
  | EP => ep
  | R1 => r1
  | R2 => r2
  | R3 => r3
  end.
*)

Definition upd (r: Reg) (p: Ptr) (rf: RegisterFile) : RegisterFile := match r with
  | IP => λ r, match r with | IP => p | _ => rf r end
  | EP => λ r, match r with | EP => p | _ => rf r end
  | R1 => λ r, match r with | R1 => p | _ => rf r end
  | R2 => λ r, match r with | R2 => p | _ => rf r end
  | R3 => λ r, match r with | R3 => p | _ => rf r end
  end.

Inductive State := st {
  st_rf : RegisterFile;
  st_p : Program;
  st_s : Stack;
  st_h  : Heap
}.

Definition I (p : Program) : State := st (λ r, 0) p nil nil. 

Open Scope nat_scope. 
Inductive read : RO → State → Ptr → Type :=
  | read_reg : ∀ r s, read (RW (WR r)) s (st_rf s r)
  | read_mem : ∀ r o rf p s h1 h2 v, 
    read (RW (WM r o)) (st rf p s (h1++(rf r+o,v)::h2)) v
  | read_const : ∀ c s, read (RC c) s c.

Inductive write : WO → Word → State → State → Type :=
  | write_reg : ∀ r rf p s h w, 
    write (WR r) w (st rf p s h) (st (upd r w rf) p s h)
  | write_mem : ∀ r o rf p s h1 h2 v w, 
    write (WM r o) w (st rf p s (h1++(rf r+o,v)::h2)) 
                     (st rf p s (h1++(rf r+o,w)::h2)).

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
  write wo w (st rf p s h) s' →
  (∀ i, i < n → not (In (w+i) (domain h))) →
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
  | step_jumpS : ∀ ro k j s s' l, 
  read ro s (S l) →
  read j s k → 
  write (WR IP) k s s' → 
  step_bb (jump (Some (ro, l)) j) s s'
  | step_jump : ∀ ro s s' l, 
  read ro s l →
  write (WR IP) l s s' → 
  step_bb (jump None ro) s s'
.

Inductive step : transition State :=
  | enter : ∀ rf p s h k bb sn,
    read IP (st rf p s h) k → 
    nth k p bb → 
    step_bb bb (st rf p s h) sn →
    step (st rf p s h) sn.

