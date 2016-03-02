Require Import cem cesm.
Require Import Unicode.Utf8.
Require Import relations. 
Require Import List. 

Notation " c1 '→_s*' c2 " := (refl_trans_clos step' c1 c2) (at level 30). 

Definition b2s (c : configuration) : stack → state := match c with
  | conf h c => λ s, st h s c end.

Definition convert_to_cesm (c c' : configuration) : Prop := match (c, c') with
  | (conf h c, conf h' c') => ∀ s, (st h s c) →_s* (st h' s c') end.

Lemma cem_cesm : ∀ c v, c ⇓ v → ∀ s, b2s c s →_s* b2s v s. 
(* Var *)
intros c v H. induction H. simpl. simpl in IHstep. 
assert (∀ s, step' (st (Υ ++ (x ↦ {M,y} :: Φ)) s (close (db.var v) z)) 
                   (st (Υ ++ (x ↦ {M,y} :: Φ)) (inr x::s) M)).
intros. apply Var. assumption. 
assert (∀ s, step' (st (Υ ++ x ↦ {M, y} :: Ψ) (inr x :: s) (close (db.lam B) e))
                   (st (Υ ++ x ↦ {close (db.lam B) e, y} :: Ψ) s (close (db.lam B) e)))
.
apply Upd. 
intros. rename y into Y.  
apply t_step with (y:=[Υ ++ x ↦ {M, Y} :: Φ, inr x :: s]M). auto. 
apply t_step2 with (y:= [Υ ++ x ↦ {M, Y} :: Ψ, inr x :: s](close (db.lam B) e)). 
auto. auto.   
(* Lam *)
intros. apply t_refl. 
(* App *)
intros. apply t_step with (y:=b2s (⟨Φ ⟩ close M e) (inl (close N e)::s)). 
apply App. 
apply refl_trans_clos_app with (y:=b2s (⟨Ψ, f ↦ {close N e, ne} ⟩ close B f) s).
apply t_step2 with (y:=b2s (⟨Ψ ⟩ close (db.lam B) ne) (inl (close N e):: s)).
simpl. rename e into E. rename s into S. apply Abs with (b:=B) (e:=ne)
(c:=close N E) (s:= S) in H.  
assumption.
auto. 
auto. 
Qed. 

Definition s2b (s : state) : configuration := match s with
  | st h s c => conf h c
  end.

Definition st_stack := λ s, match s with
  | st h s c => s
  end.


(*
Lemma cesm_cem : ∀ c c' v, c →_s c' → c' →_s* v → st_stack c = st_stack v → s2b c ⇓ s2b v.
intros. induction H0. induction H. simpl in H1. inversion v. induction H1. 
*)
