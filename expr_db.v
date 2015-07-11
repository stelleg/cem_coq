Require Vector.

Inductive expr (n : nat) : Type := 
  | var : Fin.t n -> expr n
  | lam : expr (S n) -> expr n
  | app : expr n -> expr n -> expr n.

Example term_1 : expr 0 := lam 0 (var 1 Fin.F1).
Example term_2 : expr 0 := app 0 term_1 term_1.

