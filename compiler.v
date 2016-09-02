Require expr cbn cem cesm im db assembly.
Require cbn_cem cem_cesm.
Require Import Unicode.Utf8.
Require Import util expr_db db_assembly relations.

(* This file has the high level structure of the compiler and the corresponding
main theorems of correctness *)

Definition compile (t : expr.tm) : option assembly.Program := match db t nil with
  | Some a => Some (assemble a)
  | None => None 
  end.

Notation " t `⇝c` p " := (compile t = Some p) (at level 30).

Lemma bisim_cem_st : cem.step ~ assembly.step.
Admitted.

Notation " t ≃ p " := (bisim_cem_st t p) (at level 30). 

(*
Lemma compile_bisim : ∀ t p, I
(* Definition compile (t: expr.tm) : expr.closed t → { mc | trans_clos prog p }.
*)

