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

Definition I (e : expr) : configuration := conf nil nil (close e 0).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (conf Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " :=  (conf (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (conf (append _ Ψ (cons b Φ)) N) (at level 40).

Fixpoint clu (v env:nat) (h:heap) : option (nat * closure) := match lookup eq_nat_dec env h with
    | Some (cl c env') => match v with 
      | 0 => Some (env, c) 
      | S n => clu n env' h
      end
    | None => None
  end.

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

(* Step as a function *

Lemma well_formed_lookup : ∀ l h c e, well_formed_heap h → lookup eq_nat_dec l h = Some (cl c e) →
  closed_under c h.
intros l h c e wfh lu. 

Lemma step : {c1 | well_formed c1} → {c2 | well_formed c2}.
refine (
  fun c1 => match c1 as Case1 return Case1 = c1 → {c2 | well_formed c2} with 
  | exist c p => fun case1 => match c as Case2 return c = Case2 with 
  | conf h s c' =>  match c' as Case2 return c' = with
  | close t e => match t with
    | var v => match clu v e h as Case4 return Case4 = clu v e h → {c2 | well_formed c2} with
      | Some (l, _)  => λ case4, match lookup eq_nat_dec l h as Case5
                        return Case5 = lookup eq_nat_dec l h → {c2 | well_formed c2} with
        | Some (cl c e') => λ case5, exist well_formed (conf h (inr l::s) c) _
        | None => _
      end eq_refl
      | None => _
      end eq_refl
    | lam b => match s with
      | nil => c1
      | cons (inl c) s' => let e' := new (proj1_sig c1) in 
        exist well_formed (conf ((e', cl c e)::h) s' (close b e')) _
      | cons (inr l) s' => exist well_formed 
        (conf (map (replaceClosure l (close t e)) h) s' (close t e)) _
      end
    | app m n => exist well_formed (conf h (inl (close n e):: s) (close m e)) _
    end end end
  end eq_refl
). 
unfold well_formed. split.   


*)


