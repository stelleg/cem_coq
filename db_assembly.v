Require Import List. Import ListNotations. 
Open Scope list_scope. 
Require Import db assembly util.

Infix ";" := instr (at level 30, right associativity).
Fixpoint var_inst (i : nat) : BasicBlock := match i with
  | 0 => push EP ;
         push (RC 0) ;
         mov (EP%0) R1 ;
         mov (EP%1) EP ;
         jump None R1
  | S i => mov (EP%2) EP ; 
           var_inst i
  end.


(* Assembles deBruijn indices to instructions *)
Fixpoint assemble (t : tm) (k : nat) : Program := match t with  
  | var v => [var_inst v]
  | app m n => let ms := assemble m (1+k) in
               let nk := 1+k+length ms in
                push EP ;
                push (RC nk) ;
                jump None (RC (1+k)) :: 
                ms ++ 
                assemble n nk
  | lam b => pop R1 ;
             jump (Some (RW (WR R1), (1+k))) (RC (2+k)) ::
             (*Update*)
             pop R1 ;  
             mov (RC k) (R1%0) ;
             mov EP (R1%1) ;
             jump None (RC k) ::
             (*Take*)
             new 3 R2 ;
             mov R1 (R2%0);
             pop (R2%1) ;
             mov EP (R2%2) ;
             mov R2 EP ;
             jump None (3+k) :: 
             assemble b (3+k)
  end. 

