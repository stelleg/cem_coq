Require Import db util.
Require Import Arith.EqNat.
Require Import List Unicode.Utf8 Arith.Peano_dec.
Require Import CpdtTactics.

Definition env := nat.

Record closure : Type := close {
  cl_tm : tm;
  cl_en : env
}.

Record cell : Type := cl {
  cell_cl : closure;
  cell_env : env
}.

Definition heap := Map nat cell.

Record configuration : Type := conf {
  conf_h : heap;
  conf_c : closure
}.

Definition I (e : tm) : configuration := conf nil (close e 0).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (conf Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (conf (b :: Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (conf (Ψ ++ b :: Φ) N) (at level 40).
Notation " { M , e } " := (cl M e).
Notation " < M , e > " := (close M e).

(* cactus lookup: lookup deBruijn index i at location x in heap h yields
location y *)
Inductive cactus_lookup : nat → nat → heap → (nat * cell) → Prop :=
  | zero : forall x Φ M Υ, cactus_lookup 0 x (Φ ++ (x ↦ M) :: Υ) (x, M) 
  | pred : forall x y c Φ M Υ i, cactus_lookup i x Φ c →
            cactus_lookup (S i) y (Φ ++ (y ↦ {M, x}):: Υ) c.

Fixpoint clu (v env:nat) (h:heap) : option (nat * cell) := match lookup env h with
  | None => None
  | Some (cl c a) => match v with
    | S n => clu n a h
    | 0 => Some (env, cl c a)
    end
  end.

Fixpoint update (h : heap) (l : env) (v : closure) : heap := match h with 
  | [] => []
  | (u, cl c e)::h => if beq_nat l u then (u, cl v e) :: update h l v else (u, cl c e)::update h l v
  end.

Lemma lookup_update : ∀ h l c v e, 
  lookup l h = Some (cl c e) →
  lookup l (update h l v) = Some (cl v e). 
induction h; intros. inversion H. simpl. destruct a. destruct c0. unfold lookup
in H. unfold find in H. simpl in H. destruct (beq_nat l n) eqn:bln. invert H. 
unfold lookup. unfold find. simpl. rewrite bln. reflexivity. unfold lookup.
unfold find. simpl. rewrite bln. rewrite <- (IHh l c). unfold lookup.
unfold find. reflexivity. apply H. Qed.  

Lemma lookup_update' : ∀ h l c v e l', 
  lookup l h = Some (cl c e) →
  l <> l' →
  lookup l (update h l' v) = Some (cl c e). 
induction h; intros. inversion H. simpl. destruct a. destruct c0. unfold lookup
in H. unfold find in H. simpl in H. destruct (beq_nat l n) eqn:bln. invert H.
destruct (beq_nat l' n) eqn:bln'. apply beq_nat_true in bln. apply beq_nat_true
in bln'. subst. unfold not in H0. specialize (H0 eq_refl). invert H0. unfold
lookup. unfold find. simpl. rewrite bln. reflexivity. destruct (beq_nat l' n)
eqn:bln'. unfold lookup.  unfold find. simpl. rewrite bln. erewrite <- (IHh l c).
unfold find.  reflexivity. apply H. assumption. unfold lookup. unfold find.
simpl. rewrite bln. erewrite <- (IHh l c). reflexivity. assumption.
assumption. Qed.  

Lemma domain_update : ∀ h l v, 
  domain (update h l v) = domain h. 
induction h. auto. intros. simpl. destruct a. destruct c. simpl. destruct
(PeanoNat.Nat.eqb l n); auto. simpl. rewrite IHh. reflexivity. 
simpl. rewrite IHh. reflexivity. 
Qed. 

Lemma update_nodomain : ∀ h l v, 
  l ∉ domain h → update h l v = h.
induction h. auto. intros. simpl in H. destruct a. unfold not in H. simpl in *.
destruct c. destruct (eq_nat_dec l n). subst. specialize (H (or_introl
eq_refl)). invert H. rewrite <- PeanoNat.Nat.eqb_neq in n0. rewrite n0. 
rewrite IHh. reflexivity. unfold not. intros. specialize (H (or_intror H0)).
assumption. 
Qed. 

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
  | Id : ∀ M x y z Φ Ψ v e, clu y e Φ = Some (x, {M, z}) → 
                    ⟨Φ⟩M ⇓ ⟨Ψ⟩v →
    ⟨Φ⟩close (var y) e ⇓ ⟨update Ψ x v⟩v
  | Abs : ∀ N Φ e, ⟨Φ⟩close (:λN) e ⇓ ⟨Φ⟩close (:λN) e
  | App : ∀ N M B B' Φ Ψ Υ f e ne ae, isfresh (domain Ψ) f → f > 0 →
          ⟨Φ⟩close M e ⇓ ⟨Ψ⟩close (:λB) ne → 
      ⟨Ψ, f ↦ {close N e, ne}⟩close B f ⇓ ⟨Υ⟩close (:λB') ae   →
              ⟨Φ⟩close (M@N) e ⇓ ⟨Υ⟩close (:λB') ae
where " c1 '⇓' c2 " := (step c1 c2).

Variable id_const app_const : nat.

Fixpoint time_cost {c1 c2} (s : step c1 c2) : nat := match s with 
  | Id _ _ v _ _ _ _ _ lu th => id_const * v + time_cost th
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ _ _ _ _ m b => app_const + time_cost m + time_cost b
  end. 
(*
Fixpoint stack_cost {c1 c2} (s : step c1 c2) : nat := match s with
  | Id _ _ _ _ _ _ _ _ v e => 2 + stack_cost e
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ _ _ _ m b => 2 + max (stack_cost m) (stack_cost b)
  end.

Fixpoint heap_cost {c1 c2} (s : step c1 c2) : nat := match s with
  | Id _ _ _ _ _ _ _ _ lu e => heap_cost e
  | Abs _ _ _ => 0
  | App _ _ _ _ _ _ _ _ _ _ _ _ m b => 3 + heap_cost m + heap_cost b
  end.
*)
Definition configuration' := sigT well_formed.
Definition step' (c1 c2: configuration') : Type := match (c1, c2) with
  | (existT _ c1 _, existT _ c2 _) => step c1 c2 end.

Lemma well_formed_inf : ∀ c x c' n  Φ Υ, 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c) → 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c').
  intros. split. inversion H. unfold well_formed_heap in H1. apply forevery_app in H1.
  destruct H1. simpl in H2. destruct H2. auto. 
  auto. inversion H. auto. Qed. 

Lemma values_only : ∀ c e M Ψ, c ⇓ ⟨Ψ⟩close M e → value M.
intros. induce X. 
- invert H0. apply IHX with (e:=e1) (Ψ0:=Ψ). reflexivity. 
- invert H0. simpl. constructor. 
- invert H0. apply IHX2 with (e:=e0) (Ψ:=Ψ0). reflexivity. 
Qed.

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
