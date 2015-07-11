(* Based on figure 8 of ariola et al *) 
Require Import Lists.List.
Require Import Unicode.Utf8_core.

Definition id : Type := nat.

Theorem eq_nat_dec : forall n m : id, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
    intros m.
    destruct m as [|m'].
      left. reflexivity.
      right. intros contra. inversion contra.
    intros m.
    destruct m as [|m'].
      right. intros contra. inversion contra.
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 

Inductive tm : Type :=
  | var : id -> tm
  | app : tm -> tm -> tm
  | abs : id -> tm -> tm.

Definition value (t : tm) : Prop := match t with
  | abs _ _ => True
  | _ => False
  end.


Definition heap := list (id * tm). 

Fixpoint InDomain (i:id) (h:heap) : Prop := match h with
  | cons (j,_) tail => j = i \/ InDomain i tail
  | nil => False
  end.

Example k : InDomain 3 (cons (4,var 3) (cons (3, var 4) nil)).
Proof. simpl. right. left. reflexivity. Qed. 

Inductive configuration : Type := 
  | st : heap -> tm -> configuration.

Notation " :λ x , N " := (abs x N) (at level 20).
Notation " M @ N " := (app M N) (at level 60). 
Coercion var : id >-> tm.

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (st Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (st (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (st (Datatypes.app Ψ (cons b Φ)) N) (at level 40).

Reserved Notation "'[' x '//' y ']' t" (at level 20).
Fixpoint subst (x y : id) (t : tm) : tm := match t with
  | var z => if eq_nat_dec z x then y else t
  | m@n => [x//y]m @ [x//y]n
  | :λy,b => if eq_nat_dec y x then t else (:λy,[x//y]b)
  end
where " '[' x '//' y ']' t " := (subst y x t).

(* Direct description of Maraist et al. Figure 8 *)
Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration -> configuration -> Prop :=
  | Id : ∀ M N y x Φ Ψ Υ, ⟨Φ⟩M ⇓ ⟨Ψ⟩:λy,N ->
          ⟨Φ, x ↦ M, Υ⟩x ⇓ ⟨Ψ, x ↦ :λy,N, Υ⟩:λy,N
  | Abs : ∀ N x Φ, ⟨Φ⟩:λx,N ⇓ ⟨Φ⟩:λx,N
  | App : ∀ M N L y x x' Φ Ψ Υ,⟨Φ⟩L ⇓ ⟨Ψ⟩:λx,N ->
        ⟨Ψ, x' ↦ M⟩[x'//x]N ⇓ ⟨Υ⟩:λy,N ->
           ⟨Φ⟩(L@M) ⇓ ⟨Υ⟩:λy,N
where " c1 '⇓' c2 " := (step c1 c2).

Lemma values_only : ∀ c M Ψ, c ⇓ ⟨Ψ⟩M -> value M.
intros. inversion H; simpl; auto. Qed. 

Example simple (x :id) : (step (⟨nil⟩ app (abs x x) (abs x x)) (⟨nil, x ↦ :λx,x⟩ abs x x)).
apply App with x x nil. apply Abs. simpl. destruct eq_nat_dec. rewrite <-
app_nil_l with (prod id tm) (cons (x↦:λx,x) nil). apply Id. apply Abs. unfold
not in n. assert (x = x). reflexivity. apply n in H. inversion H. Qed. 

