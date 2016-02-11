Require expr expr_db_nat cbn cem cesm.
Require Import db util assembly.
Require Import Arith.Peano_dec.
Require Import List Datatypes.
Require Import Unicode.Utf8.

(* Function instead of logical relation, not equivalent! Function takes first
value in environment, logical relation takes any. Logical relation wrong? *)

(*
Axiom refl_trans_iso : ∀ e e' m, expr.closed e → cbn.step (cbn.i e) e' → 
                assembly.step (assembly.i (compile e)) m ∧ m ≃ e'.
*)

(* TODO: Assembler from db terms.
Fixpoint assemble (e : expr_db_nat.expr) : program. *)
