Require Import db util.
Require Import Arith.EqNat.
Require Import List Unicode.Utf8 Arith.Peano_dec.
Require Import CpdtTactics.
Require Export cem. 

Definition earg {a p} : sig p → a := λ e, match e with exist _ x _ => x end.

Reserved Notation " c1 '⇓n' c2 " (at level 50).
Inductive step : configuration → configuration → Type :=
  | Id : ∀ M x z Φ Ψ y v e, clu y z Φ = Some (x, {M, e}) → 
            ⟨Φ⟩M ⇓n ⟨Ψ⟩v →
    ⟨Φ⟩close (var y) z ⇓n ⟨Ψ⟩v
  | Abs : ∀ N Φ e, ⟨Φ⟩close (:λN) e ⇓n ⟨Φ⟩close (:λN) e
  | App : ∀ N M B Φ Ψ Υ e ne v, 
          ⟨Φ⟩close M e ⇓n ⟨Ψ⟩close (:λB) ne → 
    (let f := earg (fresh (domain Ψ)) in ⟨Ψ, f ↦ {close N e, ne}⟩close B f ⇓n ⟨Υ⟩v)  →
              ⟨Φ⟩close (M@N) e ⇓n ⟨Υ⟩v 
where " c1 '⇓n' c2 " := (step c1 c2).

Variable id_const app_const : nat.

Fixpoint time_cost {c1 c2} (s : step c1 c2) : nat := match s with 
  | Id _ _ _ _ _ v _ _ lu th => id_const * v + time_cost th
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ m b => app_const + time_cost m + time_cost b
  end. 

Fixpoint stack_cost {c1 c2} (s : step c1 c2) : nat := match s with
  | Id _ _ _ _ _ _ _ _ v e => 2 + stack_cost e
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ m b => 2 + max (stack_cost m) (stack_cost b)
  end.

Fixpoint heap_cost {c1 c2} (s : step c1 c2) : nat := match s with
  | Id _ _ _ _ _ _ _ _ lu e => heap_cost e
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ m b => 3 + heap_cost m + heap_cost b
  end.

Definition configuration' := sigT well_formed.
Definition step' (c1 c2: configuration') : Type := match (c1, c2) with
  | (existT _ c1 _, existT _ c2 _) => step c1 c2 end.

Definition determ : ∀ c v v', step c v → step c v' → v = v'. 
intros. induce X. 
- invert X0. rewrite e0 in H3. invert H3. apply IHX. assumption.
- invert X0. reflexivity. 
- invert X0. apply IHX in X1. invert X1. simpl in *. apply H in X2. assumption. 
Qed. 

Definition values_only : ∀ c v, step c v → value (cl_tm (conf_c v)).
intros. induce X. 
- auto. 
- constructor. 
- simpl in *. assumption. 
Qed.

Lemma well_formed_inf : ∀ c x c' n  Φ Υ, 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c) → 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c').
  intros. split. inversion H. unfold well_formed_heap in H1. apply forevery_app in H1.
  destruct H1. simpl in H2. destruct H2. auto. 
  auto. inversion H. auto. Qed. 

(*
Lemma well_formed_inf' : ∀ Φ Ψ x c c' n,
  well_formed (⟨Φ, x ↦ cl c' n, Ψ⟩c) →
  well_formed (⟨Φ, x ↦ cl c n, Ψ⟩c).
intros. split.  inversion H. apply forevery_app in H1. destruct H1. unfold
closed_under. destruct c. unfold closed_under in H0. simpl in H2. destruct H2. 
unfold closed_under. rewrite forevery_app.  with (m:=n) (m':=n). assumption.
unfold well_formed_heap. unfold closed_under.  unfold well_formed_heap in H0.
unfold closed_under in H0. rewrite domain_inf with (m:=N) (m':=M). rewrite
forevery_app. rewrite forevery_app in H0. destruct H0. split. crush. crush. 
Qed.

TODO
Lemma cactus_lookup_inf : ∀ v x y m n e Φ Υ, cactus_lookup v x (Φ ++ (y ↦ {m, n}) :: Υ) e → ∀ M, cactus_lookup v x (Φ ++ (y ↦ {M, n}) :: Υ) e.
intros. 

Lemma inf_well_formed : ∀ c x c' n  Φ Υ, well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c) → 
  well_formed (⟨Φ, x ↦ cl c n, Υ⟩c).
  intros. inversion H. split. induction Υ. simpl. destruct c. induction (fvs e).
  simpl. auto. simpl. 
  destruct (eq_nat_dec x n0). simpl. unfold domain. rewrite
  map_app. simpl. unfold domain in H0. rewrite map_app in H0. simpl in H0. 
  kapply forevery_app in H1. destruct H1. simpl in
  H2. destruct H2. unfold closed_under in H0. clear H1 H2 H3.  (inversion H. apply forevery_app in H1.
  auto. inversion H. auto. Qed. 

Theorem well_formed_step : ∀ c v, well_formed c → c ⇓ v → well_formed v.
intros. induction H0. apply well_formed_inf in H. apply IHstep in H.  

Lemma values_only : ∀ c e M Ψ, c ⇓ ⟨Ψ⟩close M e → value M.
intros. inversion H; simpl; auto. Qed.

Example simple : (step (⟨nil⟩ close (:λ0 @ :λ0) 0) (⟨nil, 0 ↦ {close (:λ0) 0,
0}⟩ close (:λ0) 0)).
apply App with 0 nil 0 0.
unfold fresh. simpl.  auto. 
apply Abs.
rewrite <- app_nil_l with (prod nat cell) (cons (0↦{close (:λ0) 0, 0}) nil).
apply Id.
apply zero.
apply Abs. 
Qed.

*)
