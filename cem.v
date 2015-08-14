Require Import expr_db_nat.
Require Import List Unicode.Utf8_core.

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

Definition domain (h:heap) : list nat := @map (nat * cell) nat (@fst nat cell) h.

Fixpoint elem (n: nat) (d: list nat) : Prop := match d with
  | nil => False
  | cons m ms => n = m \/ elem n ms
  end.

Definition fresh (n : nat) (h : heap) (d : list nat) := 
  ~ elem n d
  /\ ~ elem n (domain h).

Reserved Notation " c1 '⇓' d '#' c2 " (at level 50).
Inductive step : configuration -> list nat -> configuration -> Prop :=
  | Id : ∀ M B x y z Φ Ψ Υ v e d, 
          cactus_lookup v z (Υ ++ (x ↦ {M,y} :: Φ)) x -> 
                ⟨Φ⟩M ⇓ cons x (domain Υ ++ d) # ⟨Ψ⟩close (:λB) e ->
    ⟨Φ, x ↦ {M, y}, Υ⟩close (var v) z ⇓ d # ⟨Ψ, x ↦ {close (:λB) e, y}, Υ⟩close (:λB) e
  | Abs : ∀ N Φ e d, ⟨Φ⟩close (:λN) e ⇓ d # ⟨Φ⟩close (:λN) e
  | App : ∀ N M B B' Φ Ψ Υ f e ne ae d, 
              fresh f Ψ d ->
          ⟨Φ⟩close M e ⇓ d # ⟨Ψ⟩close (:λB) ne ->
      ⟨Ψ, f ↦ {close N e, ne}⟩close B f ⇓ d # ⟨Υ⟩close (:λB') ae  -> 
              ⟨Φ⟩close (M@N) e ⇓ d # ⟨Υ⟩close (:λB') ae
where " c1 '⇓' d '#' c2 " := (step c1 d c2).

Lemma values_only : ∀ c e M Ψ d, c ⇓ d # ⟨Ψ⟩close M e -> value M.
intros. inversion H; simpl; auto. Qed.

Example simple : (step (⟨nil⟩ close (:λ0 @ :λ0) 0) nil (⟨nil, 0 ↦ {close (:λ0) 0,
0}⟩ close (:λ0) 0)).
apply App with 0 nil 0 0.
unfold fresh. simpl.  auto. 
apply Abs.
rewrite <- app_nil_l with (prod nat cell) (cons (0↦{close (:λ0) 0, 0}) nil).
apply Id.
apply zero.
apply Abs. 
Qed.

