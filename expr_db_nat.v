Require Import util List Arith.Peano_dec.
Inductive expr : Type := 
  | var : nat -> expr 
  | lam : expr -> expr
  | app : expr -> expr -> expr.

Definition value (t : expr) : Prop := match t with
  | lam _ => True
  | _ => False
  end.

Fixpoint fvs (e:expr) : list nat := match e with
  | var v =>  v::nil
  | lam b =>  map pred (remove eq_nat_dec 0 (fvs b))
  | app m n => fvs m ++ fvs n
  end.

Definition closed (e:expr) := fvs e = nil.

Notation " :λ N " := (lam N) (at level 20).
Notation " M @ N " := (app M N) (at level 60). 
Coercion var : nat >-> expr.

Example term_1 : expr := lam (var 0).
Example term_2 : expr := app term_1 term_1.


