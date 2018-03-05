Require expr cem cesm im db assembly.
Require curien_cem_name. 
Require Import cem_cesm cesm_im.
Require Import Unicode.Utf8.
Require Import util db_assembly relations.

(* This file has the high level structure of the compiler and the corresponding
main theorems of correctness *)

Definition compile t := assemble t 0.

Theorem compile_correct (t : db.tm) v : db.closed t → cem.step (cem.I t) v → 
  { mv : im.State & refl_trans_clos im.step (im.I (compile t)) mv *
                    state_rel (cesm.st (cem.conf_h v) nil (cem.conf_c v))
                              mv }.
Admitted.
(*Theorem compile_correct : Type := bool.
 Definition compile (t: expr.tm) : expr.closed t → { mc | trans_clos prog p }.
*)

