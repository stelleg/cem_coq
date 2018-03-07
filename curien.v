Require Import util db.  
Import ListNotations. 

Inductive closure := | close : tm → list closure → closure. 
Definition env := list closure.

Inductive step : closure → closure → Type := 
  | Abs : ∀ b e, step (close (lam b) e) (close (lam b) e)
  | Var : ∀ x e v c, nth_error e x = Some c → step c v → step (close (var x) e) v
  | App : ∀ m n b e v mve, 
      step (close m e) (close (lam b) mve) → 
      step (close b (close n e::mve)) v → 
      step (close (app m n) e) v.


