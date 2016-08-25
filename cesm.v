Require Import Arith.EqNat.
Require Import List Unicode.Utf8.
Require Import Arith.Peano_dec.
Require Import CpdtTactics.
Require Import Coq.Init.Specif.
Require Import db util.
Require Import cem relations.

Definition stack := list (closure + nat).

Record state : Type := st {
  st_heap : heap;
  st_stack : stack;
  st_closure : closure
}.

Definition state_value (s : state) : Prop := 
  value (clos_tm (st_closure s)) ∧ st_stack s = nil.

Definition I (e : tm) : state := st nil nil (close e 0).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " [ Φ , s | m ] " := (st Φ s m) (at level 80).

Definition closed (t : tm) : Prop := closed_under (close t 0) nil. 

Fixpoint lefts {a b} (l : list (a + b)) : list a := match l with
  | nil => nil
  | cons (inl a) t => cons a (lefts t)
  | cons (inr b) t => lefts t
  end.

Definition well_formed (st : state) : Prop := match st with 
  | st h s c => closed_under c h ∧ well_formed_heap h ∧ forevery (lefts s) (flip closed_under h)
                ∧ unique (domain (st_heap st))
  end.

Definition replaceClosure (l:nat) (c:closure) : nat * cell → nat * cell := 
  fun x => match x with
    | (l', cl c' e) => if eq_nat_dec l l' then (l, cl c e) else x
    end.

Reserved Notation " c1 '→s' c2 " (at level 50).
Inductive step' : state → state → Prop :=
  | Upd : ∀ Φ Υ b e e' c l s, 
  st (Φ++(l,(cl c e'))::Υ) (inr l::s) (close (lam b) e) →s 
  st (Φ++(l,(cl (close (lam b) e) e'))::Υ) s (close (lam b) e)
  | Var' : ∀ Φ s v l c e, clu v e Φ = Some (l,c) → 
  st Φ s (close (var v) e) →s st Φ (inr l::s) c
  | Abs' : ∀ Φ b e f c s p, fresh Φ = exist (isfresh Φ) f p  → 
  st Φ (inl c::s) (close (lam b) e) →s st ((f, cl c e):: Φ) s (close b f)
  | App' : ∀ Φ e s n m, 
  st Φ s (close (app m n) e) →s st Φ (inl (close n e)::s) (close m e)
where " c1 '→s' c2 " := (step' c1 c2).

Reserved Notation " c1 '→s2' c2 " (at level 50).
Inductive step2 : state → state → Prop :=
  | Upd2 : ∀ Φ c' e' l b e s, 
  lookup l Φ = Some (cl c' e') →
  st Φ (inr l::s) (close (lam b) e)  →s2
  st (replace beq_nat l (cl (close (lam b) e) e') Φ) s (close (lam b) e)
  | Var2 : ∀ Φ s v l c e, 
  clu v e Φ = Some (l,c) → 
  st Φ s (close (var v) e) →s2 st Φ (inr l::s) c
  | Abs2 : ∀ Φ b e f c s p, 
  fresh Φ = exist (isfresh Φ) f p  → 
  st Φ (inl c::s) (close (lam b) e) →s2 st ((f, cl c e):: Φ) s (close b f)
  | App2 : ∀ Φ e s n m, 
  st Φ s (close (app m n) e) →s2 st Φ (inl (close n e)::s) (close m e)
where " c1 '→s2' c2 " := (step2 c1 c2).


Lemma well_formed_upd : ∀ c l v n s Φ Υ, 
  well_formed (st (Υ ++ l ↦ cl c n :: Φ) s v) → 
  well_formed (st (Υ ++  l ↦ cl v n :: Φ) (inr l::s) v).
intros. split. inversion H. destruct H1. unfold well_formed_heap in H1. apply
forevery_app in H1.  destruct H1. simpl in H3. destruct H3. apply
closed_under_inf' with (c':= c). assumption. split. destruct H. destruct H0.
apply forevery_app. split. apply forevery_app in H0. destruct H0. refine
(forevery_impl _ _ _ _ H0). intros. destruct a. destruct c0. apply
closed_under_inf' with (c':=c). assumption. simpl. split. apply
closed_under_inf' with (c':=c). assumption. apply forevery_app in H0. destruct
H0. simpl in H2. destruct H2. refine (forevery_impl _ _ _ _ H3). intros.
destruct a. destruct c0. apply closed_under_inf' with (c':=c). assumption.
split. simpl. destruct H. destruct H0. destruct H1. refine (forevery_impl _ _ _
_ H1). intros. unfold flip. unfold flip in H3. apply closed_under_inf' with
(c':=c). assumption. destruct H. destruct H0. destruct H1. simpl. simpl in H2.
rewrite domain_inf with (m':=cl c n). assumption. Qed.

Lemma unique_step : ∀ a b, unique (domain (st_heap a)) → a →s b → 
  unique (domain (st_heap b)). 
intros. destruct H0; simpl in H; simpl; try assumption. rewrite domain_inf with
(m' := {c, e'}). assumption. apply ucons. assumption. assumption. Qed. 

Lemma forevery_lookup {B} : ∀ m p k (v:B), forevery m p → lookup k m = Some v → p (k,v).
intros. induction m. inversion H0. destruct H. destruct a. destruct (eq_nat_dec
k n). subst. unfold lookup in H0. simpl in H0. rewrite <- beq_nat_refl in H0.
inversion H0. subst. assumption. unfold lookup in H0. simpl in H0. apply
beq_nat_false_iff in n0. rewrite n0 in H0. specialize (IHm H1 H0). assumption.
Qed.

Lemma forevery_clu : ∀ x m p n c e, forevery m p → clu x e m = Some (n, c) → ∃ e',
p (n, cl c e'). intros x. induction x; intros. simpl in H0. remember (lookup e m).
destruct o. symmetry in Heqo. destruct c0. inversion H0. subst. exists n0. apply
(forevery_lookup _ _ _ _ H Heqo). inversion H0. simpl in H0. destruct (lookup e
m). destruct c0. apply (IHx m p n c n0 H H0). inversion H0. Qed.

Lemma closed_under_cons : ∀ m f cell c, fresh' f m → closed_under c m → closed_under c
  (f↦cell::m).
intros. unfold closed_under. destruct c. refine (forevery_impl _ _ _ _ H0).
intros. destruct H. destruct H1. destruct H1. exists x0, x1. destruct H1. split. 
destruct cell. apply clu_cons. assumption. assumption. apply (or_intror H2).
Qed. 

Lemma well_formed_step : ∀ a b, well_formed a → a →s b → well_formed b. 
intros. inversion H0; subst. 
apply well_formed_upd with (c:=c). assumption.
destruct H. destruct H2. destruct H3. split. apply forevery_clu with
(x:=v) (n:=l) (c:=c) (e:=e) in H2. destruct H2. assumption. assumption. split;
auto. split. destruct H. simpl in H. simpl. induction (fvs b0). auto. destruct
a. simpl. unfold lookup. simpl. rewrite <- beq_nat_refl. split. exists f, c.
auto.  apply IHl in H. assumption.  simpl. split. unfold lookup. simpl. rewrite <-
beq_nat_refl. simpl in H. destruct H. apply IHl in H3. destruct H. destruct H.
exists x, x0. split. apply clu_cons. assumption. destruct H.
assumption. destruct H. apply or_intror. assumption. apply IHl. simpl in H.
destruct H. assumption. split. unfold well_formed_heap. simpl. split; auto.
destruct H. destruct H2. destruct H3. simpl in H3. destruct H3. unfold flip in
H3. unfold closed_under. destruct c. refine (forevery_impl _ _ _ _ H3). intros.
destruct H6. destruct H6. exists x, x0. split. apply clu_cons. assumption. 
destruct H6. assumption. destruct H6. unfold In. simpl. apply
(or_intror H7). destruct H. destruct H2. refine (forevery_impl _ _ _ _ H2).
intros. destruct a. destruct c0. unfold closed_under. destruct c0. refine
(forevery_impl _ _ _ _ H4). intros. destruct H5. destruct H5. destruct H5.
exists x, x0. split; auto. apply clu_cons. assumption.
assumption. simpl. apply (or_intror H6). split. destruct H. destruct H2.
destruct H3. simpl in H3. destruct H3. refine (forevery_impl _ _ _ _ H5).
intros. unfold flip. apply closed_under_cons. split with (x:=p); assumption.
assumption. simpl. apply ucons. assumption. destruct H. destruct H2. destruct
H3. assumption. destruct H. destruct H1. destruct H2. simpl. split. simpl in H.
apply forevery_app in H. destruct H. assumption. split; auto. split. split;
auto. apply forevery_app in H. destruct H. assumption. simpl in H3. assumption.
Qed. 

Notation " c1 '→s*' c2 " := (refl_trans_clos step' c1 c2) (at level 30). 
Definition normalize (c1 c2 : state) := refl_trans_clos step' c1 c2 ∧ state_value c2.
Definition normalize2 (c1 c2 : state) := refl_trans_clos step2 c1 c2 ∧ state_value c2.
Notation " c1 '↦s*' c2 " := (normalize c1 c2) (at level 30). 

Lemma well_formed_steps : ∀ s1 s2, well_formed s1 → s1 →s* s2 → well_formed s2.
intros. induction H0. assumption. apply IHrefl_trans_clos. apply
well_formed_step with (a:=x); assumption. Qed.

Lemma step_determ : ∀ c1 c2 c3, well_formed c1 → c1 →s c2 → c1 →s c3 → c2 = c3.
intros. inversion H0; subst; inversion H1; subst. f_equal. apply unique_inf in
H3. destruct H3. destruct H3. subst. inversion H3. subst. reflexivity.
destruct H. destruct H2. apply unique_step in H1. simpl in H1. rewrite
domain_inf with (m':= {close (lam b) e,e'0}). assumption. destruct H4.
assumption. rewrite H2 in H8. inversion H8. reflexivity. rewrite H2 in H9.
inversion H9. subst. reflexivity. reflexivity. Qed. 

Lemma step2_determ : deterministic step2. 
unfold deterministic. intros. inversion H. inversion H0. subst. inversion
H5. subst. rewrite H1 in H4. inversion H4. subst. reflexivity. subst. inversion
H5. subst. inversion H5. subst. inversion H4. subst. inversion H0. subst.
rewrite H1 in H7. inversion H7. subst. reflexivity. subst. inversion H0; subst.
rewrite H1 in H8. inversion H8. subst. reflexivity. subst. inversion H0. subst.
reflexivity. Qed. 

Lemma normalize2_determ : deterministic normalize2.  
unfold deterministic. intros. destruct H. induction H. destruct H0. induction H.
reflexivity. inversion H; subst. inversion H1; subst. simpl in H5.  inversion
H5. inversion H. subst. inversion H1. inversion H4. inversion H1. inversion H5.
inversion H1. inversion H3. apply IHrefl_trans_clos. assumption. destruct H0.
destruct H0. inversion H; subst.  inversion H3. inversion H5. inversion H3.
inversion H4. inversion H3. inversion H5. inversion H3. inversion H0. apply
(step2_determ x y y0) in H. subst. split; assumption. assumption. Qed.

Lemma step'_step2 : ∀ s s', unique (domain (st_heap s)) → step' s s' → step2 s s'.
intros. induction H0; try constructor. assert (Φ ++ l ↦ cl (close (lam b) e) e'
:: Υ = replace beq_nat l (cl (close (lam b) e) e') (Φ ++ l↦(cl c e') :: Υ)).
rename c into C. rewrite replace_inf with (c:=(cl C e')).  reflexivity.
assumption.  rewrite H0. apply Upd2 with (c':=c). apply unique_domain_lookup.
assumption. exists Φ, Υ. reflexivity. assumption. apply Abs2 with (p:=p).
assumption. Qed. 

(*
Lemma lookup_unique_domain {b} : ∀ xs ys, unique (domauin
  unique (domain (Φ ++ l ↦ c :: Ψ)) →
  Φ ++ l ↦ c :: Ψ = Φ' ++ l ↦ c' :: Ψ' → Φ = Φ' ∧ Ψ = Ψ' ∧ c = c'.
intros. remember (domain (Φ ++ l↦c :: Ψ)). generalize dependent Φ. generalize
dependent c'. generalize dependent Ψ. induction H; intros; subst. unfold domain
in Heql0. rewrite map_app in Heql0. simpl in Heql0. apply app_cons_not_nil in
Heql0. inversion Heql0. unfold domain in H. rewrite map_app in H. induction Φ.
simpl in H0. induction Φ'. inversion H0. subst. auto.  inversion H0. subst.
simpl in H. inversion H; subst. unfold domain in H2. rewrite map_app in H2.
rewrite in_app_iff in H2. apply or_imp in H2. destruct H2.  simpl in H2. apply
or_imp in H2. destruct H2. specialize (H2 eq_refl). inversion H2. inversion H0.
induction Φ'. inversion H0. subst. destruct H. inversion H0.  inversion H0.
subst. remember (Φ ++ l↦c :: Ψ). apply eq_inf_indomain in Heql0.  apply H in
Heql0. inversion Heql0. inversion H0. subst. split. apply f_equal.  symmetry in
H0. apply app_eq_unit in H0. destruct H0. destruct H0. subst. inversion H1.
subst. auto. inversion H0.  subst. inversion H2. inversion H0. inversion_clear
H; subst. simpl in H1. apply or_imp in H1. destruct H1. apply ucons with (v:=c)
in H1. simpl in IHΨ.  specialize (IHΨ H1). induction Φ'. inversion H0. subst.
auto. simpl in H0.  inversion H0. subst. apply eq_inf_indomain in H5.  simpl in
IHΦ'. destruct H5.  crush. inversion H1. crush. inversion H0. apply
eq_inf_indomain in H5. apply IHΦ'.  simpl in H0. 

unfold not in H1.
simpl in H1. destruct incrush. apply app_eq_unit in H0.  
  
Lemma step_determ : deterministic (λ c c', unique_domain (st_heap c) ∧ step' c c').  
unfold deterministic. intros. crush. inversion H2; inversion H3; subst; crush;
auto. inversion H5; subst. 

Lemma normalize2_determ : deterministic normalize2.  


 Step as a function *
Lemma well_formed_step : ∀ s s', well_formed s → s →s s' → well_formed s'. 
intros.  induction H0. apply well_formed_inf. 

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


