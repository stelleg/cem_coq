Require Import Unicode.Utf8 util cesm im db db_assembly assembly relations List cem. 

Definition prog_eq (p : Ptr) (pr : Program) (t : tm) := 
  let subpr := assemble t p in subpr = firstn (length subpr) (skipn p pr).

Inductive env_eq : nat → cem.heap → 
                   Program → Ptr → im.Heap → Type := 
  | ee : ∀ n ch pr p ih e e' c c' ip t, 
    lookup n ch = Some (cl (close t e) c) →
    lookup p ih = Some ip → 
    lookup (p+1) ih = Some e' → 
    lookup (p+2) ih = Some c' → 
    prog_eq ip pr t → 
    env_eq e ch pr e' ih →    
    env_eq c ch pr c' ih →    
    env_eq n ch pr p ih.
    
(*
Inductive state_rel : cesm.state → im.State → Type := 
  | str : ∀ cs is, 
  prog_eq (st_rf is IP) (st_p is) (cl_tm (st_cl cs)) →
  env_eq (st_rf is IP) (st_p is) (cl_tm (st_cl im)) →
  state_rel cs is.
*)

Lemma cesm_im : ∀ v s s', 
  state_rel s s' → 
  refl_trans_clos cesm.step s v → 
  sigT (fun v' =>  refl_trans_clos im.step s' v').
Admitted.

Lemma cesm_im_assemble : ∀ t v v', 
  refl_trans_clos cesm.step (cesm.I t) v → 
  refl_trans_clos step (I (assemble t 1)) v'.
Admitted.

