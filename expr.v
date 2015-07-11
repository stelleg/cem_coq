
Definition id : Type := nat.

Inductive tm : Type :=
  | var : id -> tm
  | app : tm -> tm -> tm
  | abs : id -> tm -> tm.

Definition value (t : tm) : Prop := match t with
  | abs _ _ => True
  | _ => False
  end.

Notation " :λ x , N " := (abs x N) (at level 20).
Notation " M @ N " := (app M N) (at level 60). 
Coercion var : id >-> tm.

