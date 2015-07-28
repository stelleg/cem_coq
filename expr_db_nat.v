Inductive expr : Type := 
  | var : nat -> expr 
  | lam : expr -> expr
  | app : expr -> expr -> expr.

Definition value (t : expr) : Prop := match t with
  | lam _ => True
  | _ => False
  end.

Notation " :λ N " := (lam N) (at level 20).
Notation " M @ N " := (app M N) (at level 60). 
Coercion var : nat >-> expr.

Example term_1 : expr := lam (var 0).
Example term_2 : expr := app term_1 term_1.


