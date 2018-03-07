Require Import Arith.EqNat.
Require Import List Unicode.Utf8.
Require Import Arith.Peano_dec.
Require Import CpdtTactics.
Require Import db util.
Require Import cem relations.

Definition stack := list (closure + nat).
Definition heap := cem.heap.
Definition closure := cem.closure.

Inductive state : Type := st {
  st_hp : heap; 
  st_st : stack;
  st_cl : closure
}.

Definition I (e : tm) : state := st nil nil (close e 0).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " [ Φ , s ] m " := (st Φ s m) (at level 40).

Definition closed (t : tm) : Prop := closed_under (close t 0) nil. 

Fixpoint lefts {a b} (l : list (a + b)) : list a := match l with
  | nil => nil
  | cons (inl a) t => cons a (lefts t)
  | cons (inr b) t => lefts t
  end.

Definition well_formed (st : state) : Prop := match st with 
  | st h s c => closed_under c h ∧ well_formed_heap h ∧ forevery (lefts s) (flip closed_under h)
  end.

Definition replaceClosure (l:nat) (c:closure) : nat * cell → nat * cell := 
  fun x => match x with
    | (l', cl c' e) => if eq_nat_dec l l' then (l, cl c e) else x
    end.

Reserved Notation " c1 '→_s' c2 " (at level 50).
Inductive step : transition state :=
  | Upd : ∀ Φ b e l s, 
  st Φ (inr l::s) (close (lam b) e) →_s 
  st (update Φ l (close (lam b) e)) s (close (lam b) e)
  | Var : ∀ Φ s v l c e e', clu v e Φ = Some (l,cl c e') → 
  st Φ s (close (var v) e) →_s st Φ (inr l::s) c
  | Abs : ∀ Φ b e f c s, isfresh (domain Φ) f → 
  st Φ (inl c::s) (close (lam b) e) →_s st ((f, cl c e):: Φ) s (close b f)
  | App : ∀ Φ e s n m, 
  st Φ s (close (app m n) e) →_s st Φ (inl (close n e)::s) (close m e)
where " c1 '→_s' c2 " := (step c1 c2).

Fixpoint transition_fold 
  {a b : Type} {s : transition a} (st en : a) 
  (f:forall x y, s x y → b → b) 
  (xs:refl_trans_clos s st en) 
  (y:b) 
  : b :=
  match xs with 
  | t_refl _ _ => y 
  | t_step _ x y' z t xs => @transition_fold a b s y' z f xs (f x y' t y) 
  end.  

Definition step_time_cost (x y : state) (s : step x y) : nat := match s with
  | _ => 1
  end.

Definition time_cost (x y : state) (s : refl_trans_clos step x y) : nat :=
  transition_fold x y (fun x y s b => plus (step_time_cost x y s) b) s 0.

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


