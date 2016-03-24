(* Based on figure 8 of ariola et al *) 
Require Import Lists.List EqNat Decidable CpdtTactics Program.Basics.
Require Import Unicode.Utf8_core.
Require Import expr util.
Require Import Arith.Peano_dec.

Definition heap := list (nat * tm). 

Record configuration : Type := st {
  st_heap : heap;
  st_tm : tm
}.

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (st Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (st (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (st (Datatypes.app Ψ (cons b Φ)) N) (at level 40).

Definition I (e : tm ) : configuration := st nil e.

(* Direct description of Maraist et al. Figure 8, with amendment from  *)
Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M N y x Φ Ψ Υ, ⟨Φ, x ↦ M, Υ⟩M ⇓ ⟨Ψ, x ↦ M, Υ⟩:λy,N →
            ⟨Φ, x ↦ M, Υ⟩var x ⇓ ⟨Ψ, x ↦ :λy,N, Υ⟩:λy,N
  | Abs : ∀ N x Φ,  ⟨Φ⟩:λx,N ⇓ ⟨Φ⟩:λx,N
  | App : ∀ M N L B y x x' Φ Ψ Υ,
              fresh' x' Ψ → 
            ⟨Φ⟩L ⇓ ⟨Ψ⟩:λx,N → 
        ⟨Ψ, x' ↦ M⟩[var x'//x]N ⇓ ⟨Υ⟩:λy,B →
           ⟨Φ⟩(L@M) ⇓ ⟨Υ⟩:λy,B
where " c1 '⇓' c2 " := (step c1 c2).

Lemma values_only : ∀ c M Ψ, c ⇓ ⟨Ψ⟩M → value M.
intros. inversion H; simpl; auto. Qed. 

Definition closed_under (c : configuration) : Prop := match c with
  | st h t => subset (fvs t) (domain h) end.

Definition closed (t : tm) : Prop := closed_under (st nil t).

Definition well_formed_heap (h : heap) : Prop := unique (domain h) ∧ forevery h (λ p, match p with
  | (x, M) => closed_under (st h M)
  end).

Definition well_formed (c : configuration) : Prop := match c with 
  | st h t => closed_under c ∧ well_formed_heap h 
  end.

Lemma well_formed_app : ∀ (Φ Ψ:heap) (x:nat) (M N:tm), 
  well_formed (⟨Φ, x ↦ M, Ψ⟩N) →
  well_formed (⟨Φ, x ↦ M, Ψ⟩M).
intros. destruct H. clear H. split. unfold well_formed_heap in H0. destruct H0. apply
forevery_inf in H0. assumption. auto. Qed. 

Lemma well_formed_app' : ∀ (Φ Ψ:heap) (x:nat) (M N:tm), 
  well_formed (⟨Φ, x ↦ M, Ψ⟩N) →
  well_formed (⟨Φ, x ↦ N, Ψ⟩N).
intros. simpl in H. destruct H. split. unfold closed_under. rewrite domain_inf
with (m:=N) (m':=M). assumption. unfold well_formed_heap. unfold closed_under.
unfold well_formed_heap in H0. unfold closed_under in H0. rewrite domain_inf
with (m:=N) (m':=M). rewrite forevery_app. rewrite forevery_app in H0. destruct
H0. split. crush. crush. Qed.

Lemma unique_step : ∀ s s', unique (domain (st_heap s)) → step s s' → unique
(domain (st_heap s')). 
intros. induction H0. simpl. simpl in IHstep. rewrite <- domain_inf with (m:=M).
apply IHstep. assumption. assumption. simpl. simpl in IHstep2. simpl in IHstep1.
apply IHstep2. simpl in H. apply ucons. unfold fresh' in H0. destruct H0.
assumption. apply IHstep1. assumption. Qed. 

Lemma not_vars_fvs : ∀ n e, ~(In n (vars e)) -> ~(In n (fvs e)).
induction e. simpl. intros. assumption. simpl. rewrite in_app_iff. rewrite
in_app_iff. intros. apply not_or in H. destruct H. apply IHe1 in H. apply IHe2
in H0. unfold not. intros. destruct H1. apply H in H1. assumption. apply H0 in
H1. assumption. simpl. intros. apply not_or in H. destruct H. apply IHe in H0.
unfold not. intros. unfold not in H. assert (n <> n0). unfold not. intros.
symmetry in H2.  apply H in H2. assumption. apply remove_not_in with (ns:=fvs e)
in H2. apply H2 in H1. apply H0 in H1. assumption. Qed.  

Lemma monotonic_heap : ∀ c1 c2, c1 ⇓ c2 → domain (st_heap c1) ⊆ domain (st_heap c2).  
intros c1 c2 step.  induction step. simpl. simpl in IHstep. 
unfold domain at 2. unfold domain at 2 in IHstep. rewrite map_app. rewrite
map_app in IHstep.  simpl. simpl in IHstep. assumption. 
apply subset_id. simpl. simpl in IHstep1. simpl in IHstep2. destruct IHstep2. 
apply subset_trans with (ys:=domain Ψ). assumption. assumption. Qed.

Theorem well_formed_step : ∀ c1 c2, well_formed c1 → c1 ⇓ c2 → well_formed c2.
intros. induction H0. apply well_formed_app in H. apply IHstep in H. apply
well_formed_app' in H. assumption. assumption. apply IHstep2. 
simpl in H. destruct H. rewrite app_subset_and in H. destruct H. assert
(well_formed (⟨Φ ⟩ L)). split; assumption. apply IHstep1 in H3. clear IHstep2. 
split. Focus 2. unfold well_formed_heap. simpl. split. assert (subset (domain Φ)
(domain Ψ)). apply monotonic_heap in H0_. assumption. destruct H3. apply ucons.
unfold fresh' in H0. destruct H0.  assumption. destruct H5. assumption. split.
apply subset_cons. apply monotonic_heap in H0_. simpl in H0_. apply subset_trans
with (ys := (domain Φ)) (zs:= (domain Ψ)) in H2; assumption.  unfold well_formed
in H3. destruct H3. unfold well_formed_heap in H4. unfold closed_under in H4.
apply forevery_impl with (p:=(λ p:nat*tm, let (_,M0) := p in subset (fvs M0)
(domain Ψ))). intros. destruct a. apply subset_cons. assumption. destruct H4.
assumption. simpl. simpl in H3. destruct H3. assert (subset (fvs ([x' // x]N))
(fvs x' ++ remove x (fvs N))).  apply subst_subset.  simpl in H5. apply
(cons_subset x') in H3. apply subset_trans with (ys:=x'::remove x (fvs N)).
assumption. assumption. Qed. 

Lemma det_step : ∀ a b c, well_formed a → a ⇓ b → a ⇓ c → b = c. 
intros a b c wf s. generalize dependent c. induction s. apply well_formed_app in
wf. specialize (IHs wf). intros. inversion H. subst. symmetry in H0. apply
unique_inf in H0; try (destruct wf; destruct H2; assumption). destruct H0.
destruct H1. subst. apply IHs in H3. inversion H3. subst. apply app_eq_l in H1.
inversion H1.  subst. reflexivity. intros. inversion H. subst. auto. inversion 
wf. simpl in H0. rewrite app_subset_and in H0. destruct H0. specialize (IHs1
(conj H0 H1)). assert (s1':=s1). apply well_formed_step in s1; try (apply (conj
H0 H1)). destruct s1. assert (s1:=s1'). simpl in H3. apply monotonic_heap in s1.
simpl in s1. apply subset_trans with (xs:=fvs M) in s1; try assumption. assert
(well_formed_heap (x' ↦ M :: Ψ)). split. simpl. apply ucons. destruct H.
assumption. inversion H4. assumption. simpl. split. apply subset_cons.
assumption. inversion H4. unfold closed_under in H6. apply forevery_impl with
(p:=λ p, let (_,M0) := p : nat * tm in fvs M0 ⊆ domain Ψ). intros. destruct a.
apply subset_cons. assumption. assumption. assert (fvs ([x'//x]N) ⊆ (x'::domain Ψ)).
apply subset_trans with (ys:=fvs (var x') ++ remove x (fvs N)). apply
subst_subset. simpl. split. apply or_introl. reflexivity. apply subset_cons.
assumption. assert (well_formed (⟨Ψ, x' ↦ M⟩[x'//x]N)). split. assumption.
assumption. specialize (IHs2 H7). intros. inversion H8. subst. apply IHs1 in
H14. inversion H14. subst. destruct H12. inversion H9. destruct H. rewrite H in
H9. inversion H9. subst. apply IHs2 in H15. assumption. Qed. 

(* Collapsing configuration to term 
Fixpoint collapse (h : heap) : tm → tm :=  match h with
  | nil => id 
  | cons (x, e') t => compose (subst x (collapse t e')) (collapse t)
  end.

Example collapse_simple : collapse (0↦:λ0, 0  :: nil) 0 = :λ0, 0.
eauto. Qed. 

Lemma well_formed_collapse : forall h, well_formed_heap h -> 
  ∀ n t, In n (fvs (collapse h t)) -> In n (fvs t) /\ ~In n (domain h).
intros h wf. induction h. crush. destruct a. intros. simpl in wf. destruct wf.
simpl in H. unfold compose in H.  assert (subset (fvs ([collapse h t //
n]collapse h t0)) (fvs (collapse h t) ++ remove n (fvs (collapse h t0)))). apply
subst_subset. rewrite <- subset_eq in H2. apply H2 in H. clear H2. rewrite in_app_iff in
H. destruct H.  rewrite <- subset_eq in H0. apply IHh in H. crush. assumption. 
destruct (eq_nat_dec n0 n). subst. apply remove_in in H. inversion H. apply
remove_not_in in H. apply IHh in H. crush. assumption. assumption. Qed.

Lemma well_formed_collapse_closed : forall h t, well_formed_heap h ->
closed_under (st h t) -> closed (collapse h t).
intros. assert (∀ n t, In n (fvs (collapse h t)) -> In n (fvs t) /\ ~In n
(domain h)). apply well_formed_collapse. assumption. unfold closed. unfold
closed_under. simpl. rewrite <- subset_eq. unfold subset'. intros. apply H1 in
H2. simpl. destruct H2. unfold closed_under in H0. rewrite <- subset_eq in H0.
apply H0 in H2. apply H3 in H2. assumption. Qed. 

*)
