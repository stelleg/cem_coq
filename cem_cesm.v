Require Import cem cesm relations util.

Notation " c1 '→_s*' c2 " := (refl_trans_clos cesm.step c1 c2) (at level 30). 

Definition b2s (c : configuration) : stack → state := match c with
  | conf h c => λ s, st h s c end.

Definition convert_to_cesm (c c' : configuration) : Type := match (c, c') with
  | (conf h c, conf h' c') => ∀ s, (st h s c) →_s* (st h' s c') end.

Lemma cem_cesm : ∀ Φ Ψ c v, conf Φ c ⇓ conf Ψ v → ∀ s, st Φ s c →_s* st Ψ s v. 
intros. induce X; intros; invert H1; invert H0. 
(* Var *)
- destruct v0. apply values_only in X. inversion X. 
  specialize (IHX _ _ _ _ (inr x::s) eq_refl eq_refl).   
  apply t_step with (y0:=[Φ0, inr x :: s]M). 
  + apply Var with (e':=z). assumption. 
  + apply t_step2 with (y0:= [Ψ, inr x :: s]close cl_tm cl_en). 
    * subst. apply Upd.  
    * assumption.  
(* Lam *)
- intros. apply t_refl. 
(* App *)
- intros. apply t_step with (y:=(st Φ0 (inl (close N e)::s)) (close M e)). 
  + apply App. 
  + apply refl_trans_clos_app with (y:=b2s (⟨Ψ, f ↦ {close N e, ne} ⟩ close B f) s).
    * apply t_step2 with (y:=b2s (⟨Ψ ⟩ close (db.lam B) ne) (inl (close N e):: s)).
      -- simpl. rename e into E. rename s into S. 
         apply Abs with (b:=B) (e:=ne) (c:=close N E) (s:= S). 
         assumption. assumption.
      -- apply IHX1. reflexivity. reflexivity.  
    * simpl. apply IHX2. reflexivity. reflexivity.  
Qed. 

(*
Lemma cem_cesm_time : ∀ c v (e:c ⇓ v) s, 
  sigT (fun x => time_cost (b2s c s) (b2s v s) x = cem.time_cost e). 
induction e.  
- intros s. simpl in IHe.  

Definition s2b (s : state) : configuration := match s with
  | st h s c => conf h c
  end.

Definition st_stack := λ s, match s with
  | st h s c => s
  end.


Lemma cesm_cem : ∀ c c' v, c →_s c' → c' →_s* v → st_stack c = st_stack v → s2b c ⇓ s2b v.
intros. induction H0. induction H. simpl in H1. inversion v. induction H1. 
*)
