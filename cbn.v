(* Based on figure 8 of ariola et al *) 
Require Import Lists.List.
Require Import Unicode.Utf8_core.
Require Import expr.
Require Import Arith.Peano_dec.

Definition heap := list (id * tm). 

Fixpoint InDomain (i:id) (h:heap) : Prop := match h with
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

Reserved Notation "'[' x '//' y ']' t" (at level 20).
Fixpoint subst (x x' : id) (t : tm) : tm := match t with
  | var y => if eq_nat_dec y x then x else t
  | m@n => [x'//x]m @ [x'//x]n
  | :λy,b => if eq_nat_dec y x then t else (:λy,[x'//x]b)
  end
where " '[' x '//' y ']' t " := (subst y x t).

(* Direct description of Maraist et al. Figure 8 *)
Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration -> configuration -> Prop :=
  | Id : ∀ M N y x Φ Ψ Υ, ⟨Φ⟩M ⇓ ⟨Ψ⟩:λy,N ->
          ⟨Φ, x ↦ M, Υ⟩x ⇓ ⟨Ψ, x ↦ :λy,N, Υ⟩:λy,N
  | Abs : ∀ N x Φ, ⟨Φ⟩:λx,N ⇓ ⟨Φ⟩:λx,N
  | App : ∀ M N L B y x x' Φ Ψ Υ,⟨Φ⟩L ⇓ ⟨Ψ⟩:λx,N ->
        ⟨Ψ, x' ↦ M⟩[x'//x]N ⇓ ⟨Υ⟩:λy,B ->
           ⟨Φ⟩(L@M) ⇓ ⟨Υ⟩:λy,B
where " c1 '⇓' c2 " := (step c1 c2).

Lemma values_only : ∀ c M Ψ, c ⇓ ⟨Ψ⟩M -> value M.
intros. inversion H; simpl; auto. Qed. 

Example simple (x y :id) : (step (⟨nil⟩ ((:λx,x) @ (:λy,y))) (⟨nil, x ↦ :λy,y⟩ :λy, y)).
apply App with x x x nil. apply Abs. simpl. destruct eq_nat_dec. rewrite <-
app_nil_l with (prod id tm) (cons (x↦:λy,y) nil). rewrite <- app_nil_l with
(prod id tm) (cons (x↦:λy,y) nil). apply Id. apply Abs. unfold not in n.
assert (x = x). reflexivity. apply n in H. inversion H. Qed. 


