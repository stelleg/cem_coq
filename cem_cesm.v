Require Import cem cesm relations List.
Require Import Unicode.Utf8.
Require cem cesm.

Notation " c1 '→_s*' c2 " := (refl_trans_clos cesm.step c1 c2) (at level 30). 

Definition b2s (c : configuration) : stack → state := match c with
  | conf h c => λ s, st h s c end.

Definition convert_to_cesm (c c' : configuration) : Type := match (c, c') with
  | (conf h c, conf h' c') => ∀ s, (st h s c) →_s* (st h' s c') end.

Lemma cem_cesm : ∀ c v, c ⇓ v → ∀ s, b2s c s →_s* b2s v s. 
intros c v H. induction H.
(* Var *)
- simpl. simpl in IHstep. intros. rename y into Y.  
  apply t_step with (y:=[Υ ++ x ↦ {M, Y} :: Φ, inr x :: s]M). auto. 
  + apply Var. assumption. 
  + apply t_step2 with (y:= [Υ ++ x ↦ {M, Y} :: Ψ, inr x :: s](close (db.lam B) e)). 
    * apply Upd. 
    * auto. 
(* Lam *)
- intros. apply t_refl. 
(* App *)
- intros. apply t_step with (y:=b2s (⟨Φ ⟩ close M e) (inl (close N e)::s)). 
  + apply App. 
  + apply refl_trans_clos_app with (y:=b2s (⟨Ψ, f ↦ {close N e, ne} ⟩ close B f) s).
    * apply t_step2 with (y:=b2s (⟨Ψ ⟩ close (db.lam B) ne) (inl (close N e):: s)).
      -- simpl. rename e into E. rename s into S. 
         apply Abs with (b:=B) (e:=ne) (c:=close N E) (s:= S). 
         assumption. 
      -- auto. 
    * auto. 
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
