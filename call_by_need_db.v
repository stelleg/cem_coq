(* Based on figure 8 of Maraist et al *) 
Require Import Lists.List.
Require Import Unicode.Utf8_core.
Require Import expr_db.
Require Import Vector.
Require Import Arith.Peano_dec.

Inductive closure n := 
  | close : expr n -> t nat n -> closure n.

Definition heap := list (nat * forall n, closure n). 

Inductive configuration : Type := 
  | st : heap -> (forall n, closure n) -> configuration.

Notation " x // c " := (match c with 
  | close exp env => close exp (cons _ x env) end) (at level 40).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (st Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (st (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (st (Datatypes.app Ψ (cons b Φ)) N) (at level 40).

(* Natural Semantics from Maraist et al. Figure 8 *)
Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration -> configuration -> Prop :=
  | Id : ∀ c b be x Φ Ψ Υ, ⟨Φ⟩c ⇓ ⟨Ψ⟩(close :λb be) ->
        ⟨Φ, x ↦ c, Υ⟩x ⇓ ⟨Ψ, x ↦ (close :λb be), Υ⟩(close :λb be)
  | Abs : ∀ N x Φ, ⟨Φ⟩:λN ⇓ ⟨Φ⟩:λN
  | App : ∀ M N L B y x x' Φ Ψ Υ,⟨Φ⟩L ⇓ ⟨Ψ⟩:λN ->
        ⟨Ψ, x' ↦ M⟩x'//N ⇓ ⟨Υ⟩:λB ->
           ⟨Φ⟩(L@M) ⇓ ⟨Υ⟩:λB
where " c1 '⇓' c2 " := (step c1 c2).

Lemma values_only : ∀ c M Ψ, c ⇓ ⟨Ψ⟩M -> value M.
intros. inversion H; simpl; auto. Qed. 

Example simple (x y :id) : (step (⟨nil⟩ ((:λx,x) @ (:λy,y))) (⟨nil, x ↦ :λy,y⟩ :λy, y)).
apply App with x x x nil. apply Abs. simpl. destruct eq_nat_dec. rewrite <-
app_nil_l with (prod id tm) (cons (x↦:λy,y) nil). rewrite <- app_nil_l with
(prod id tm) (cons (x↦:λy,y) nil). apply Id. apply Abs. unfold not in n.
assert (x = x). reflexivity. apply n in H. inversion H. Qed. 


