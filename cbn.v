(* Based on figure 8 of ariola et al *) 
Require Import Lists.List Decidable CpdtTactics Program.Basics.
Require Import Unicode.Utf8_core.
Require Import expr util.
Require Import Arith.Peano_dec.

Definition heap := list (nat * tm). 

Inductive configuration : Type := 
  | st : heap -> tm -> configuration.

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (st Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (st (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (st (Datatypes.app Ψ (cons b Φ)) N) (at level 40).

Definition domain (h:heap) : list nat := @map (nat * tm) nat (@fst nat tm) h.
Definition fresh (n : nat) (e : tm) (h : heap) (d : list nat) := ~ In n d
  /\ ~ In n (vars e)
  /\ ~ In n (domain h).

(* Direct description of Maraist et al. Figure 8, with amendment from  *)
Reserved Notation " c1 '⇓' d '#' c2 " (at level 50).
Inductive step : configuration -> list nat -> configuration -> Prop :=
  | Id : ∀ M N y x Φ d Ψ Υ, ⟨Φ⟩M ⇓ cons x (List.app (domain Υ) d) # ⟨Ψ⟩:λy,N ->
          ⟨Φ, x ↦ M, Υ⟩var x ⇓ d # ⟨Ψ, x ↦ :λy,N, Υ⟩:λy,N
  | Abs : ∀ N x Φ d,  ⟨Φ⟩:λx,N ⇓ d # ⟨Φ⟩:λx,N
  | App : ∀ M N L B y x x' Φ Ψ Υ d d',
              fresh x' N Φ d ->
            ⟨Φ⟩L ⇓ d # ⟨Ψ⟩:λx,N ->
        ⟨Ψ, x' ↦ M⟩[var x'//x]N ⇓ d' # ⟨Υ⟩:λy,B ->
           ⟨Φ⟩(L@M) ⇓ d # ⟨Υ⟩:λy,B
where " c1 '⇓' d '#' c2 " := (step c1 d c2).

Lemma values_only : ∀ c M Ψ d, c ⇓ d # ⟨Ψ⟩M -> value M.
intros. inversion H; simpl; auto. Qed. 

Definition closed_under (c : configuration) : Prop := match c with
  | st h t => subset (fvs t) (domain h) end.

Definition closed (t : tm) : Prop := closed_under (st nil t).

Fixpoint well_formed_heap (h : heap) : Prop := match h with
  | cons (x, M) t => closed_under (st t M)  /\ well_formed_heap t 
  | nil => True
  end.

Definition well_formed (c : configuration) : Prop := match c with 
  | st h t => closed_under c /\ well_formed_heap h 
  end.

Fixpoint collapse (h : heap) : tm -> tm :=  match h with
  | nil => id 
  | cons (x, e') t => compose (subst x (collapse t e')) (collapse t)
  end.

Example collapse_simple : collapse (0↦:λ0, 0  :: nil) 0 = :λ0, 0.
eauto. Qed. 

Lemma well_formed_app : ∀ (Φ Ψ:heap) (x:nat) (M N:tm), 
  well_formed (⟨Φ, x ↦ M, Ψ⟩N) ->
  well_formed (⟨Φ⟩ M).
intros. 
destruct H.  
clear H.
induction Ψ.
destruct H0. split; assumption. simpl in H0. apply IHΨ.
destruct a. destruct H0. assumption.  Qed.

Definition stheap (c:configuration) : heap := match c with | st h t => h end.
Definition sttm (c:configuration) : tm := match c with | st h t => t end.

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

Lemma not_vars_fvs : forall n e, ~(In n (vars e)) -> ~(In n (fvs e)).
induction e. simpl. intros. assumption. simpl. rewrite in_app_iff. rewrite
in_app_iff. intros. apply not_or in H. destruct H. apply IHe1 in H. apply IHe2
in H0. unfold not. intros. destruct H1. apply H in H1. assumption. apply H0 in
H1. assumption. simpl. intros. apply not_or in H. destruct H. apply IHe in H0.
unfold not. intros. unfold not in H. assert (n <> n0). unfold not. intros.
symmetry in H2.  apply H in H2. assumption. apply remove_not_in with (ns:=fvs e)
in H2. apply H2 in H1. apply H0 in H1. assumption. Qed.  

Lemma fresh_subst : forall x x' e h d, fresh x' e h d -> fvs ([x'//x]e) = replace x x' (fvs e).
intros. destruct H. destruct H0. induction e. simpl in H0. apply not_or in H0.
destruct H0. simpl. unfold replace'. destruct (eq_nat_dec x n); simpl; auto. simpl. unfold
replace. rewrite map_app. simpl in H0. rewrite in_app_iff in H0. apply
not_or in H0. destruct H0. apply IHe1 in H0. apply IHe2 in H2. rewrite H0.
rewrite H2. reflexivity. simpl. destruct (eq_nat_dec x n). simpl. subst. rewrite
replace_remove. auto.  simpl. simpl in H0. apply not_or in H0. destruct H0.
assert (not (In x' (fvs e))). apply not_vars_fvs in H2. assumption.
apply IHe in H2. rewrite H2. induction (fvs e). auto. simpl. simpl in H2. unfold
replace' in H2. unfold replace'. 
destruct (eq_nat_dec x a). destruct (eq_nat_dec n x'). apply H0 in e1. inversion
e1. destruct (eq_nat_dec n a). subst. rewrite replace_remove. assert (a = a).
reflexivity. apply n0 in H4. inversion H4. subst. simpl. unfold replace'. rewrite
eq_nat_dec_refl. simpl in H3. apply not_or in H3. destruct H3. apply
remove_replace_comp with (y:=a) (z:=n) in H4 . rewrite H4. reflexivity.
assumption. assumption. unfold not. intros. simpl in H3. apply not_or in H3. destruct H3. destruct (eq_nat_dec n
a). subst. apply remove_replace_comp. assumption. assumption. unfold not.
intros. symmetry in H5. apply n0 in H5. assumption. simpl. unfold replace'. destruct (eq_nat_dec
x a). apply n1 in e0. inversion e0. apply remove_replace_comp with (y:=x)
(z:=n) in H4. rewrite H4. reflexivity. assumption. auto. Qed. 

Lemma monotonic_heap : forall c1 c2 d, c1 ⇓ d # c2 -> 
subset (domain (stheap c1)) (domain (stheap c2)).  
intros. 
induction H. 
simpl.  simpl in IHstep. unfold domain. rewrite map_app. rewrite map_app. unfold
domain in IHstep. simpl. apply subset_comm1. simpl. split. apply
in_or_app. right. simpl. auto. 
apply subset_comm1. simpl. apply subset_app_id. apply subset_cons. assumption.
apply subset_id. simpl. simpl in IHstep1. simpl in IHstep2. destruct IHstep2.
apply subset_trans with (ys:=domain Ψ); assumption. Qed.

Lemma well_formed_var : forall Φ Ψ Υ x n v, well_formed (⟨Ψ, x↦n, Υ⟩x) -> subset
  (domain Ψ) (domain Φ) -> well_formed (⟨Φ⟩v) -> well_formed (⟨Φ, x↦v, Υ⟩v).
intros. split. simpl. unfold domain. rewrite map_app. apply subset_comm2. apply
subset_app.  apply subset_cons. destruct H1. unfold closed_under in H1.
assumption. inversion H as [H' H2].  induction Υ. simpl. destruct H1. unfold
closed_under in H1. split; assumption.  destruct a. simpl in H2. destruct H2.
simpl. split. unfold domain. rewrite map_app.  unfold domain in H2. rewrite
map_app in H2.  apply subset_comm2 in H2. simpl in H2. apply subset_comm2.
simpl.  rewrite cons_app. rewrite cons_app in H2. rewrite app_comm_cons.
rewrite app_comm_cons in H2. apply subset_comm2. rewrite <- app_assoc. apply
subset_comm2 in H2.  rewrite <- app_assoc in H2. apply subset_comm2. apply
subset_comm2 in H2.  unfold domain in H0. apply subset_app_id with (xs :=
((((map (fst (B:=tm)) Υ ++ x :: nil))))) in H0. apply subset_trans with (ys :=
((map (fst (B:=tm)) Υ ++ x :: nil) ++ map (fst (B:=tm)) Ψ)). assumption.
assumption.  apply well_formed_app in H.  destruct H. clear H'. clear H4. unfold
closed_under in H. apply subset_app with (zs:=domain (Υ ++ x↦n :: nil)) in H.
assert (well_formed (⟨Ψ, x ↦n, Υ ⟩ x)). split. unfold closed_under. unfold
domain.  rewrite map_app. apply subset_comm2. simpl. auto. assumption. apply
IHΥ.  assumption. destruct H4. assumption. assumption. Qed.

Theorem well_formed_step : ∀ c1 c2 d, well_formed c1 -> c1 ⇓ d # c2 -> well_formed c2.
intros. induction H0. assert (well_formed (⟨Φ, x ↦ M, Υ⟩x)). assumption. split. 
apply well_formed_app in H. apply IHstep in H. unfold closed_under. 
unfold domain. rewrite map_app. apply subset_comm2. apply
subset_app. apply subset_cons.  destruct H. assumption. 
apply monotonic_heap in H0. simpl in H0. apply well_formed_var with (Ψ:=Φ)
(Φ:=Ψ) (x:=x) (v:=:λy,N) in H. inversion H. assumption. assumption. apply
well_formed_app in H. apply IHstep in H. assumption. assumption. 
destruct H. unfold closed_under in H. simpl in H. apply app_subset_and in H. destruct H.
assert (well_formed (⟨Φ ⟩ L)). split; assumption. assert (well_formed (⟨Φ ⟩ M)).
split; assumption. apply IHstep1 in H3.  assert (well_formed (⟨Ψ, x' ↦ M ⟩ [x'
// x]N)). split. unfold closed_under. simpl. apply fresh_subst with (x:=x) in
H0. rewrite H0. apply replace_cons. destruct H3. simpl in H3. apply subset_remove_cons
in H3. assumption.  apply monotonic_heap in H0_. simpl in H0_. split. unfold
closed_under. destruct H4. unfold closed_under in H4. apply subset_trans with
(ys:=domain Φ); assumption. destruct H3. assumption. apply IHstep2 in H5.
assumption. Qed.

Example simple : (step (⟨nil⟩ ((:λ0,0) @ (:λ0,0))) nil (⟨nil, 1 ↦ :λ0,0⟩ :λ0,0)).
apply App with 0 0 1 nil nil. unfold fresh.  simpl. split; auto. split. unfold
not. intros. destruct H. inversion H. assumption. auto. apply Abs. simpl. rewrite <-
app_nil_l with (prod nat tm) (cons (1↦:λ0,0) nil). rewrite <- app_nil_l with
(prod nat tm) (cons (1↦:λ0,0) nil). apply Id. apply Abs. Qed. 

