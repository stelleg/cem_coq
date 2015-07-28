Require Vector.

Definition db_ind := Fin.t.
Inductive expr (n : nat) : Type := 
  | var : db_ind n -> expr n
  | lam : expr (S n) -> expr n
  | app : expr n -> expr n -> expr n.

Definition value {n} (t : expr n) : Prop := match t with
  | lam _ => True
  | _ => False
  end.

Notation " :λ N " := (forall n, lam n N) (at level 20).
Notation " M @ N " := (forall n, app n M N) (at level 60). 
Coercion var : db_ind >-> expr.

Example term_1 : expr 0 := lam 0 (var 1 Fin.F1).
Example term_2 : expr 0 := app 0 term_1 term_1.


