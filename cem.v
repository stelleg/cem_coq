Require Import db util.
Require Import Arith.EqNat.
Require Import List Unicode.Utf8 Arith.Peano_dec.
Require Import CpdtTactics.

Definition append := Datatypes.app.

Record closure : Type := close {
  clos_tm : tm;
  clos_env : nat
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

Fixpoint clu (v env:nat) (h:heap) : option (nat * closure) := match lookup env h with
  | None => None
  | Some (cl c a) => match v with
    | S n => clu n a h
    | 0 => Some (env, c)
    end
  end.

Definition isfresh (h : heap) (n : nat) : Prop := ¬ In n (domain h). 
Axiom fresh : ∀ h:heap, @sig nat (isfresh h). 

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
Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M B x y z Φ Ψ Υ v e, clu v z (Υ ++ x ↦ {M,y} :: Φ) = Some (x, M) → 
            ⟨Φ, (x ↦ {M,y}), Υ⟩M ⇓ ⟨Ψ, (x ↦ {M,y}), Υ⟩close (:λB) e →
    ⟨Φ, x ↦ {M, y}, Υ⟩close (var v) z ⇓ ⟨Ψ, x ↦ {close (:λB) e, y}, Υ⟩close (:λB) e
  | Abs : ∀ N Φ e, ⟨Φ⟩close (:λN) e ⇓ ⟨Φ⟩close (:λN) e
  | App : ∀ N M B B' Φ Ψ Υ f e ne ae p, 
                fresh Ψ = exist (isfresh Ψ) f p → 
          ⟨Φ⟩close M e ⇓ ⟨Ψ⟩close (:λB) ne → 
      ⟨Ψ, f ↦ {close N e, ne}⟩close B f ⇓ ⟨Υ⟩close (:λB') ae   →
              ⟨Φ⟩close (M@N) e ⇓ ⟨Υ⟩close (:λB') ae
where " c1 '⇓' c2 " := (step c1 c2).

Definition configuration' := sig well_formed.
Definition step' (c1 c2: configuration') : Prop := match (c1, c2) with
  | (exist c1 _, exist c2 _) => step c1 c2 end.

Lemma well_formed_inf : ∀ c x c' n  Φ Υ, 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c) → 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c').
intros. split. inversion H. unfold well_formed_heap in H1. apply forevery_app in H1.
destruct H1. simpl in H2. destruct H2. auto. 
auto. inversion H. auto. Qed. 

Lemma forevery_cons {A} : ∀ (p:A→Prop) (x:A) xs, p x → forevery xs p → forevery (x::xs) p. 
intros. simpl. split; assumption. Qed. 

(*

Lemma closed_under_inf' : ∀ c c' e x Ψ Φ, closed_under c (Φ ++ x ↦ {c', e} :: Ψ) →
  closed_under c (Φ ++ x ↦ {c, e} :: Ψ).
intros. unfold closed_under. destruct c. unfold closed_under in H. induction (fvs clos_tm0). simpl. auto.
simpl. split. simpl in H. destruct H. destruct H. destruct H. destruct H.
destruct (clu a clos_env0 (Φ ++ x ↦ {c', e} :: Ψ)). destruct p. inversion H.
destruct c. destruct = 
destruct H. 
apply
ex_intro with x0. apply ex_intro with x1. split. destapply forevery_inf with (xs:=Φ)
(ys:=Ψ) (y:=x ↦ {, e}). . .  forevery_app in H. 

Lemma well_formed_inf' : ∀ Φ Ψ x c c' n,
  well_formed (⟨Φ, x ↦ cl c' n, Ψ⟩c) →
  well_formed (⟨Φ, x ↦ cl c n, Ψ⟩c).
intros. split.  inversion H. apply forevery_app in H1. destruct H1. simpl in H2. destruct H2. rename x into X. apply forevery_cons
with (x:=X ↦ {c', n}) (xs:=Φ) in H0. assumption. apply  . assumption.  in H0. assert (conj H0 H3). forevery (x ↦ {c, n} :: Φ), λ
x0, match x0 with _ ↦ {c1, _} => closed_under c1 (append (nat * cell) Ψ (x ↦ {c',
n} :: Φ)) end). 
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
