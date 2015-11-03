(* Based on figure 8 of ariola et al *) 
Require Import Lists.List.
Require Import Unicode.Utf8_core.
Require Import expr util.
Require Import Arith.Peano_dec.

Definition heap := list (nat * tm). 

Fixpoint InDomain (i:nat) (h:heap) : Prop := match h with
  | cons (j,_) tail => j = i \/ InDomain i tail
  | nil => False
  end.

Example k : InDomain 3 (cons (4,var 3) (cons (3, var 4) nil)).
Proof. simpl. right. left. reflexivity. Qed. 

Inductive configuration : Type := 
  | st : heap -> tm -> configuration.

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (st Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (st (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (st (Datatypes.app Ψ (cons b Φ)) N) (at level 40).

Definition domain (h:heap) : list nat := @map (nat * tm) nat (@fst nat tm) h.

Lemma head_elem : forall h tail,  elem h (cons h tail).
  intros. simpl. left. reflexivity. Qed.

Definition fresh (n : nat) (e : tm) (h : heap) (d : list nat) := 
  ~ elem n d
  /\ ~ elem n (fvs e)
  /\ ~ elem n (domain h).

(* Direct description of Maraist et al. Figure 8, with amendment from  *)
Reserved Notation " c1 '⇓' d '#' c2 " (at level 50).
Inductive step : configuration -> list nat -> configuration -> Prop :=
  | Id : ∀ M N y x Φ d Ψ Υ, ⟨Φ⟩M ⇓ cons x (List.app (domain Υ) d) # ⟨Ψ⟩:λy,N ->
          ⟨Φ, x ↦ M, Υ⟩var x ⇓ d # ⟨Ψ, x ↦ :λy,N, Υ⟩:λy,N
  | Abs : ∀ N x Φ d,  ⟨Φ⟩:λx,N ⇓ d # ⟨Φ⟩:λx,N
  | App : ∀ M N L B y x x' Φ Ψ Υ d d',
              fresh x' N Φ d ->
            ⟨Φ⟩L ⇓ d # ⟨Ψ⟩:λx,N ->
        ⟨Ψ, x' ↦ M⟩[var x'//x]N ⇓ d' # ⟨Υ⟩:λy,B ->
           ⟨Φ⟩(L@M) ⇓ d # ⟨Υ⟩:λy,B
where " c1 '⇓' d '#' c2 " := (step c1 d c2).

Lemma values_only : ∀ c M Ψ d, c ⇓ d # ⟨Ψ⟩M -> value M.
intros. inversion H; simpl; auto. Qed. 

Example simple : (step (⟨nil⟩ ((:λ0,0) @ (:λ0,0))) nil (⟨nil, 1 ↦ :λ0,0⟩ :λ0,0)).
apply App with 0 0 1 nil nil. unfold fresh.  simpl. split; auto. split. unfold
not. intros. destruct H. inversion H. assumption. auto. apply Abs. simpl. rewrite <-
app_nil_l with (prod nat tm) (cons (1↦:λ0,0) nil). rewrite <- app_nil_l with
(prod nat tm) (cons (1↦:λ0,0) nil). apply Id. apply Abs. Qed. 

