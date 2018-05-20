Require expr cem cesm im db assembly.
Require curien_cem_name. 
Require Import cem_cesm cesm_im.
Require Import Unicode.Utf8.
Require Import util db_assembly relations.

(* This file has the high level structure of the compiler and the corresponding
main theorems of correctness *)

Definition compile t := assemble t 0.

Theorem compile_correct (t : db.tm) v : cem.step (cem.I t) v → 
  sigT (λ v', refl_trans_clos im.step (im.I (compile t)) v' *
              state_rel (cesm.st (cem.conf_h v) nil (cem.conf_c v)) v').
intros. unfold cem.I in X. destruct v. eapply cem_cesm with (s := []) in
X. assert (csi := eq_refl (cesm.I t)). unfold cesm.I in csi at 1. rewrite csi
in X. simpl. apply cesm_im_assemble. assumption. Qed.


