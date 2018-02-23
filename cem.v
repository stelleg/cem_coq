Require Import db util.
Require Import Arith.EqNat.
Require Import List Unicode.Utf8 Arith.Peano_dec.
Require Import CpdtTactics.

Definition append := Datatypes.app.

Inductive closure : Type := close {
  cl_tm : tm;
  cl_en : nat
}.

Inductive cell : Type :=
  | cl : closure → nat → cell.

Definition clclose (c: cell) : closure := match c with cl c e => c end.

Definition heap := Map nat cell.

Inductive configuration : Type :=
  | conf : heap → closure → configuration.

Definition I (e : tm) : configuration := conf nil (close e 0).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (conf Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (conf (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (conf (append _ Ψ (cons b Φ)) N) (at level 40).
Notation " { M , e } " := (cl M e).
Notation " < M , e > " := (close M e).

(* cactus lookup: lookup deBruijn index i at location x in heap h yields
location y *)
Inductive cactus_lookup : nat → nat → heap → nat → Prop :=
  | zero : forall x Φ M Υ, cactus_lookup 0 x (Φ ++ (x ↦ M) :: Υ) x
  | pred : forall x y z Φ M Υ i, cactus_lookup i x Φ z → 
            cactus_lookup (S i) y (Φ ++ (y ↦ {M, x}):: Υ) z.

Definition lookup {a} (x:nat) (l:list (nat * a)) : option a := 
  match find (λ p, beq_nat x (fst p)) l with 
    | None => None
    | Some (k,v) => Some v
  end.

Fixpoint clu (v env:nat) (h:heap) : option (nat * closure) := match lookup env h with
  | None => None
  | Some (cl c a) => match v with
    | S n => clu n a h
    | 0 => Some (env, c)
    end
  end.

Definition fresh (n : nat) (h : heap) := 
  ~ In n (domain h).

Definition closed_under (c : closure) (h : heap)  : Prop := match c with
  | close t e => forevery (fvs t) 
      (λ x, ∃e' c', clu x e h = Some (e',c') ∧ In e' (domain h))
  end.

Definition closed (t : tm) : Prop := closed_under (close t 0) nil.

Definition well_formed_heap (h : heap) : Prop := forevery h 
  (λ x, match x with | (v,cl c e') => closed_under c h end). 

Definition well_formed (c : configuration) : Prop := match c with 
  | conf h t => closed_under t h ∧ well_formed_heap h 
  end.

Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration → configuration → Type :=
  | Id : ∀ M B x y z Φ Ψ Υ v e, clu v z (Υ ++ x ↦ {M,y} :: Φ) = Some (x, M) → 
            ⟨Φ, (x ↦ {M,y}), Υ⟩M ⇓ ⟨Ψ, (x ↦ {M,y}), Υ⟩close (:λB) e →
    ⟨Φ, x ↦ {M, y}, Υ⟩close (var v) z ⇓ ⟨Ψ, x ↦ {close (:λB) e, y}, Υ⟩close (:λB) e
  | Abs : ∀ N Φ e, ⟨Φ⟩close (:λN) e ⇓ ⟨Φ⟩close (:λN) e
  | App : ∀ N M B B' Φ Ψ Υ f e ne ae, fresh f Ψ → 
          ⟨Φ⟩close M e ⇓ ⟨Ψ⟩close (:λB) ne → 
      ⟨Ψ, f ↦ {close N e, ne}⟩close B f ⇓ ⟨Υ⟩close (:λB') ae   →
              ⟨Φ⟩close (M@N) e ⇓ ⟨Υ⟩close (:λB') ae
where " c1 '⇓' c2 " := (step c1 c2).

Fixpoint time_cost {c1 c2} (s : step c1 c2) : nat := match s with 
  | Id _ _ _ _ _ _ _ _ _ _ lu e => 1 + time_cost e
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ _ _ _ m b => 1 + time_cost m + time_cost b
  end. 

Fixpoint stack_cost {c1 c2} (s : step c1 c2) : nat := match s with
  | Id _ _ _ _ _ _ _ _ _ _ lu e => 1 + stack_cost e
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ _ _ _ m b => 1 + max (stack_cost m) (stack_cost b)
  end.

Fixpoint heap_cost {c1 c2} (s : step c1 c2) : nat := match s with
  | Id _ _ _ _ _ _ _ _ _ _ lu e => heap_cost e
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ _ _ _ m b => 1 + heap_cost m + heap_cost b
  end.

Definition configuration' := sigT well_formed.
Definition step' (c1 c2: configuration') : Type := match (c1, c2) with
  | (existT _ c1 _, existT _ c2 _) => step c1 c2 end.

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
