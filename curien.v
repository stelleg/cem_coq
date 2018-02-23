Require Import Unicode.Utf8 List db util.  
Import ListNotations. 

Inductive closure := | close : tm → list closure → closure. 
Definition env := list closure.

Inductive step : closure → closure → Prop := 
  | abs : ∀ b e, step (close (lam b) e) (close (lam b) e)
  | var : ∀ x e v c, nth x e c → step c v → step (close (var x) e) v
  | app : ∀ m n b e v mve, 
      step (close m e) (close (lam b) mve) → 
      step (close b (close n e::mve)) v → 
      step (close (app m n) e) v.


