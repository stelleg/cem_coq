Require Import expr_db_nat.
Require Import Unicode.Utf8_core.

Definition append := Datatypes.app.

Inductive closure : Type := 
  | close : expr -> nat -> closure. 

Inductive cell : Type :=
  | cl : closure -> nat -> cell.

Definition heap := list (prod nat cell).

Inductive configuration : Type :=
  | st : heap -> closure -> configuration.

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (st Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (st (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (st (append _ Ψ (cons b Φ)) N) (at level 40).
Notation " { M , e } " := (cl M e).
Notation " < M , e > " := (close M e).

Inductive cactus_lookup : nat -> nat -> heap -> nat -> Prop :=
  | zero : forall x Φ M Υ, cactus_lookup 0 x (append _ Φ (cons (x ↦ M) Υ)) x
  | pred : forall x y z Φ M Υ i, cactus_lookup i x Φ z -> 
            cactus_lookup (S i) y (append _ Φ (cons (y ↦ {M, x}) Υ)) z.

Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration -> configuration -> Prop :=
  | Id : ∀ M V x y z Φ Ψ Υ v, cactus_lookup v z Φ x -> ⟨Φ⟩M ⇓ ⟨Ψ⟩V ->
      ⟨Φ, x ↦ {M, y}, Υ⟩close (var v) z ⇓ ⟨Ψ, x ↦ {V, y}, Υ⟩V
  | Abs : ∀ N Φ e, ⟨Φ⟩close (:λN) e ⇓ ⟨Φ⟩close (:λN) e
  | App : ∀ N M Φ Ψ Υ V f e ne, ⟨Φ⟩close M e ⇓ ⟨Ψ⟩close (:λN) ne ->
      ⟨Ψ, f ↦ {close M e, ne}⟩close N f ⇓ ⟨Υ⟩V -> 
              ⟨Φ⟩close (M@N) e ⇓ ⟨Υ⟩V
where " c1 '⇓' c2 " := (step c1 c2).

