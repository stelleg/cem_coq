Require Import Arith.EqNat.
Require Import List Unicode.Utf8.
Require Import Arith.Peano_dec.
Require Import CpdtTactics.
Require Import expr_db_nat util.

Definition append := Datatypes.app.

Inductive closure : Type := 
  | close : expr → nat → closure. 

Inductive cell : Type :=
  | cl : closure → nat → cell.

Definition heap := list (nat * cell).

Definition stack := list (closure + nat).

Inductive configuration : Type :=
  | conf : heap → stack → closure → configuration.

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (conf Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " :=  (conf (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (conf (append _ Ψ (cons b Φ)) N) (at level 40).

Fixpoint clu (v env:nat) (h:heap) : option nat := match v with
  | 0 => Some env
  | S n => match lookup eq_nat_dec env h with
    | Some (cl c a) => clu n a h
    | None => None
    end
  end.

Definition domain (h:heap) : list nat := @map (nat * cell) nat (@fst nat cell) h.

Definition fresh (n : nat) (h : heap) := 
  ~ In n (domain h).

Definition c_hp (c : configuration) := match c with
  | conf h s c => h end.

Axiom new : ∀ (c : configuration), nat.
Axiom new_fresh : ∀ c, fresh (new c) (c_hp c).

Inductive cactus_lookup : nat → nat → heap → nat → Prop :=
  | zero : forall x Φ M Υ, cactus_lookup 0 x (append _ Φ (cons (x ↦ M) Υ)) x
  | pred : forall x y z Φ M Υ i, cactus_lookup i x Φ z → 
            cactus_lookup (S i) y (append _ Φ (cons (y ↦ (cl M x)) Υ)) z.

Definition closed_under (c : closure) (h : heap) : Prop := match c with
  | close t e => forevery (fvs t) 
      (λ x, ∃e', cactus_lookup x e h e' ∧ In e' (domain h))
  end.

Definition closed (t : expr) : Prop := closed_under (close t 0) nil. 

Definition well_formed_heap (h : heap) : Prop := forevery h 
  (λ x, match x with | (v,cl c e) => closed_under c h end). 

Fixpoint lefts {a b} (l : list (a + b)) : list a := match l with
  | nil => nil
  | cons (inl a) t => cons a (lefts t)
  | cons (inr b) t => lefts t
  end.

Definition well_formed (conf : configuration) : Prop := match conf with 
  | conf h s c => closed_under c h ∧ well_formed_heap h ∧ forevery (lefts s) (flip closed_under h)
  end.

Definition replaceClosure (l:nat) (c:closure) : nat * cell → nat * cell := 
  fun x => match x with
    | (l', cl c' e) => if eq_nat_dec l l' then (l, cl c e) else x
    end.

Definition step : {c1 | well_formed c1} → {c2 | well_formed c2}.
refine (
  fun c1 => match c1 with
  | exist (conf h s (close t e)) p => match t with
    | var v => match clu v e h with
      | Some l => match lookup eq_nat_dec l h with
        | Some (cl c e') => exist well_formed (conf h (inr l::s) c) _
        | None => _
        end
      | None => _
      end
    | lam b => match s with
      | nil => c1
      | cons (inl c) tl => let e' := new (proj1_sig c1) in 
        exist well_formed (conf ((e', cl c e)::h) tl (close b e')) _
      | cons (inr l) tl => exist well_formed 
        (conf (map (replaceClosure l (close t e)) h) tl (close t e)) _
      end
    | app m n => exist well_formed (conf h (inl (close n e):: s) (close m e)) _
    end
  end
).
split. 
destruct x. 
destruct p. 

Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M B x y z Φ Ψ Υ v e, 
                  cactus_lookup v z (Υ ++ (x ↦ {M,y} :: Φ)) x →
              ⟨Φ, (x ↦ {M,y}), Υ⟩M ⇓ ⟨Ψ, (x ↦ {M,y}), Υ⟩close (:λB) e →
    ⟨Φ, x ↦ {M, y}, Υ⟩close (var v) z ⇓ ⟨Ψ, x ↦ {close (:λB) e, y}, Υ⟩close (:λB) e
  | Abs : ∀ N Φ e, ⟨Φ⟩close (:λN) e ⇓ ⟨Φ⟩close (:λN) e
  | App : ∀ N M B B' Φ Ψ Υ f e ne ae, fresh f Ψ → 
          ⟨Φ⟩close M e ⇓ ⟨Ψ⟩close (:λB) ne → 
      ⟨Ψ, f ↦ {close N e, ne}⟩close B f ⇓ ⟨Υ⟩close (:λB') ae   →
              ⟨Φ⟩close (M@N) e ⇓ ⟨Υ⟩close (:λB') ae
where " c1 '⇓' c2 " := (step c1 c2).

Lemma well_formed_inf : ∀ c x c' n  Φ Υ, well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c) → 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c').
  intros. split. inversion H. unfold well_formed_heap in H1. apply forevery_app in H1.
  destruct H1. simpl in H2. destruct H2. auto. 
  auto. inversion H. auto. Qed. 

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


