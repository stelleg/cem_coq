Require expr cbn cem cesm im db assembly.
Require cbn_cem cem_cesm.
Require Import Unicode.Utf8.
Require Import util expr_db db_assembly.

(* This file has the high level structure of the compiler and the corresponding
main theorems of correctness *)

Definition compile (t : expr.tm) : option assembly.Program := match db t nil with
  | Some a => Some (assemble a 0)
  | None => None 
  end.

(*Theorem compile_correct : Type := bool.
 Definition compile (t: expr.tm) : expr.closed t → { mc | trans_clos prog p }.
*)

