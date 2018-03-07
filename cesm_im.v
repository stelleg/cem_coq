Require Import util cesm im db db_assembly assembly relations List cem.
Import ListNotations.

Variable new : ∀ (n:nat) (h : im.Heap), sigT (λ w:nat, ∀ i, lt i n → (plus w i) ∉ domain h).

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
  
Inductive clos_eq : cem.closure → cem.heap → 
                    Ptr → Ptr → Program → im.Heap → 
                    Type :=
  | c_eq : ∀ t e ch p ip ep ih, 
           prog_eq ip p t → 
           env_eq e ch p ep ih →
           clos_eq (cem.close t e) ch ip ep p ih.

Inductive stack_eq : cesm.stack → cesm.heap →
                     im.Stack → Program → im.Heap → Type := 
  | stack_nil : ∀ ch p ih, 
                stack_eq nil ch nil p ih
  | stack_upd : ∀ e ch p ep ih cs is, 
                 env_eq e ch p ep ih →
                 stack_eq cs ch is p ih →
                 stack_eq (inr e::cs) ch (0::ep::is) p ih
  | stack_arg : ∀ ch p ip ep ih cs is c, 
                 clos_eq c ch ip ep p ih →
                 stack_eq cs ch is p ih → 
                 stack_eq (inl c::cs) ch (ip::ep::is) p ih.

Inductive state_rel : cesm.state → im.State → Type := 
  | str : ∀ cs is, 
  clos_eq (st_cl cs) (st_hp cs) (st_rf is IP) (st_rf is EP) (st_p is) (st_h is) →
  stack_eq (st_st cs) (st_hp cs) (st_s is) (st_p is) (st_h is) →
  state_rel cs is.

Lemma cesm_im : ∀ v s s', 
  state_rel s s' → 
  cesm.step s v → 
  sigT (λ v', refl_trans_clos im.step s' v' * state_rel v v').
intros v s s' r h. induce h. 
- invert r. invert X. 
  
Admitted.

Lemma cesm_im_assemble : ∀ t v v', 
  refl_trans_clos cesm.step (cesm.I t) v → 
  refl_trans_clos im.step (im.I (assemble t 1)) v'.
Admitted.

