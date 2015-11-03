Require Import FSets.FSetInterface List util.
Require Import Arith.Peano_dec.

Inductive tm : Type :=
  | var : nat -> tm
  | app : tm -> tm -> tm
  | abs : nat -> tm -> tm.

Definition value (t : tm) : Prop := match t with
  | abs _ _ => True
  | _ => False
  end.

Notation " :λ x , N " := (abs x N) (at level 20).
Notation " M @ N " := (app M N) (at level 60). 
Coercion var : nat >-> tm.

Fixpoint fvs (e:tm) : list nat := match e with
  | var v => cons v nil
  | abs v b => filter (compose negb (neq_bool v)) (fvs b)
  | app m n => List.app (fvs m) (fvs n)
  end.

Reserved Notation "'[' x '//' y ']' t" (at level 20).
Fixpoint subst (x : nat) (x' : tm) (t : tm) : tm := match t with
  | var y => if eq_nat_dec y x then x' else t
  | m@n => [x'//x]m @ [x'//x]n
  | :λy,b => if eq_nat_dec y x then t else (:λy,[x'//x]b)
  end
where " '[' x '//' y ']' t " := (subst y x t).

Lemma ex1 : fvs (var 1) = cons 1 nil.
simpl. reflexivity. Qed.

Lemma ex2 : fvs (abs 1 (var 1)) = nil.
simpl. reflexivity. Qed.

Lemma ex3 : fvs (app (var 1) (var 1)) = cons 1 (cons 1 nil).
simpl. reflexivity. Qed.
