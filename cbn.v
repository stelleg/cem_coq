(* Based on figure 8 of ariola et al *) 
Require Import Lists.List EqNat Decidable CpdtTactics Program.Basics.
Require Import Unicode.Utf8_core.
Require Import expr util.
Require Import Arith.Peano_dec.
Import ListNotations. 

Definition heap := list (nat * tm). 

Record configuration : Type := st {
  reachable : heap;
  unreachable : heap;
  st_tm : tm
}.

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Ψ & Φ ⟩ m " := (st Ψ Φ m) (at level 40).
Notation " ⟨ Υ & b , Φ , Ψ ⟩ N " := (st Υ (Ψ ++ Φ ++ b :: nil) N) (at level 40).
Notation " ⟨ Υ , b & Ψ ⟩ N " := (st (b :: Υ) Ψ N) (at level 40).
Notation " ⟨ Υ , b , Φ & Ψ ⟩ N " := (st (Φ ++ b :: Υ) Ψ N) (at level 40).

Definition I (e : tm ) : configuration := st nil nil e.

(* Direct description of Maraist et al. Figure 8, with amendment for freshness  *)
Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M N y x Φ Υ Ψ Ψ', ⟨Ψ & x ↦ M, Φ, Υ⟩M ⇓ ⟨Ψ' & x ↦ M, Φ, Υ⟩:λy,N →
            ⟨Ψ, x ↦ M, Φ & Υ⟩ x ⇓ ⟨Ψ', x ↦ :λy,N, Φ & Υ⟩:λy,N
  | Abs : ∀ N x Φ Ψ, ⟨Ψ & Φ⟩:λx,N ⇓ ⟨Ψ & Φ⟩:λx,N
  | App : ∀ M N L B y x x' Φ Ψ Υ Φ',
              fresh' x' (Ψ ++ Φ') → 
            ⟨Φ & Ψ⟩L ⇓ ⟨Φ' & Ψ⟩:λx,N → 
        ⟨Φ', x' ↦ M & Ψ⟩[var x'//x]N ⇓ ⟨Υ & Ψ⟩:λy,B →
           ⟨Φ & Ψ⟩(L@M) ⇓ ⟨Υ & Ψ⟩:λy,B
where " c1 '⇓' c2 " := (step c1 c2).

Lemma values_only : ∀ c M Ψ Φ, c ⇓ ⟨Φ & Ψ⟩M → value M.
intros. inversion H; simpl; auto. Qed. 

Definition closed_under (t : tm) (h : heap) : Prop := fvs t ⊆ domain h. 

Definition closed (t : tm) : Prop := closed_under t nil.

Fixpoint well_formed_heap (h : heap) : Prop := match h with
  | nil => True
  | (v,t)::h => isfresh h v ∧  closed_under t h ∧ well_formed_heap h
  end. 
  
Definition well_formed (c : configuration) : Prop := match c with 
  | st r ur t => closed_under t r  ∧ well_formed_heap (ur ++ r) 
  end.

Lemma well_formed_heap_app : ∀ Φ Ψ, well_formed_heap (Φ ++ Ψ) → well_formed_heap Ψ. 
intros. induction Φ. assumption. apply IHΦ. destruct a. destruct H. destruct H0.
assumption. Qed. 

Lemma well_formed_app : ∀ (Υ Φ Ψ:heap) (x:nat) (M N:tm), 
  well_formed (⟨Φ, x ↦ M, Ψ & Υ⟩N) →
  well_formed (⟨Φ & x ↦ M, Ψ, Υ⟩M).
intros. destruct H. split. apply well_formed_heap_app in H0.  apply
well_formed_heap_app in H0. inversion H0. destruct H2. assumption. rewrite <-
app_assoc. rewrite <- app_assoc. simpl. assumption. Qed.

Lemma well_formed_app' : ∀ (Φ Ψ Υ:heap) (x:nat) (M N:tm), 
  well_formed (⟨Φ & x ↦ M, Ψ, Υ⟩N) →
  well_formed (⟨Φ & x ↦ N, Ψ, Υ⟩N).
intros. destruct H. split. assumption. repeat (rewrite <- app_assoc in H0). 
set (h := (Υ ++ Ψ)). fold h in H0. assert (h = Υ ++ Ψ).
auto. rewrite app_assoc. rewrite app_assoc in H0. rewrite <- H1 in *. clear H1. induction
h. simpl in *. destruct H0. destruct H1. split; try auto. destruct a. split.
inversion H0. unfold isfresh. rewrite <- app_assoc. simpl.  rewrite domain_inf with (m':=M). assumption.
split. inversion H0. destruct H2. unfold closed_under. rewrite <- app_assoc.
simpl. rewrite domain_inf with (m':=M). assumption. apply IHh. inversion H0.
destruct H2. auto. Qed.

Lemma well_formed_weaken_reach : ∀ (Φ Ψ Υ:heap) (x:nat) (M N:tm), 
  well_formed (⟨Φ & x ↦ N, Ψ, Υ⟩M) →
  well_formed (⟨Φ, x ↦ N, Ψ & Υ⟩M).
intros. destruct H. split. unfold closed_under. apply subset_trans with
(ys:=domain Φ). assumption. unfold domain. rewrite map_app. unfold domain. apply
subset_app_weaken. simpl. apply subset_cons. apply subset_id. repeat (rewrite <-
app_assoc in H0). assumption. Qed.  

Definition st_heap st := unreachable st ++ reachable st. 

Lemma well_formed_heap_has_unique_domain : ∀ h, well_formed_heap h → unique (domain h).
intros. induction h. apply unil. destruct a. apply ucons. simpl. inversion H.
assumption. apply IHh. inversion H. destruct H1. assumption. Qed. 

Hint Unfold domain. 
Hint Rewrite map_app. 
Hint Rewrite <- map_app.
Hint Resolve in_app_or.  
Hint Resolve in_or_app.
Hint Unfold not. 
Hint Resolve or_comm. 

Lemma unique_step : ∀ s s', unique (domain (st_heap s)) → step s s' → unique (domain (st_heap s')). 
intros. induction H0. unfold st_heap in *. simpl in *. rewrite app_assoc.
rewrite <- domain_inf with (m:=M). rewrite <- app_assoc. rewrite <- app_assoc in
IHstep. rewrite <- app_assoc in IHstep. rewrite <- app_assoc in IHstep. rewrite
<- app_assoc in IHstep. simpl in IHstep. apply IHstep. assumption. assumption. 
unfold st_heap in *. simpl in *. apply IHstep2. rewrite unique_domain_app.
simpl. apply ucons. unfold fresh' in H0. destruct H0. unfold not. intros. apply
x0. unfold domain. rewrite map_app. apply in_or_app. apply or_comm. apply
in_app_or. rewrite <- map_app. assumption.  rewrite unique_domain_app. apply
IHstep1. assumption. Qed. 

Lemma not_vars_fvs : ∀ n e, ~(In n (vars e)) -> ~(In n (fvs e)).
induction e. simpl. intros. assumption. simpl. rewrite in_app_iff. rewrite
in_app_iff. intros. apply not_or in H. destruct H. apply IHe1 in H. apply IHe2
in H0. unfold not. intros. destruct H1. apply H in H1. assumption. apply H0 in
H1. assumption. simpl. intros. apply not_or in H. destruct H. apply IHe in H0.
unfold not. intros. unfold not in H. assert (n <> n0). unfold not. intros.
symmetry in H2.  apply H in H2. assumption. apply remove_not_in with (ns:=fvs e)
in H2. apply H2 in H1. apply H0 in H1. assumption. Qed.  

Lemma monotonic_reachable : ∀ c1 c2, c1 ⇓ c2 → domain (reachable c1) ⊆ domain
(reachable c2).  
intros c1 c2 step.  induction step; simpl in *. unfold domain. rewrite map_app.
rewrite map_app. apply subset_app_id. simpl. split. apply or_introl.
reflexivity. apply subset_cons. assumption. apply subset_id. destruct IHstep2.
apply subset_trans with (ys:=domain Φ'); assumption. Qed.  

Lemma monotonic_heap : ∀ c1 c2, c1 ⇓ c2 → domain (st_heap c1) ⊆ domain (st_heap c2).  
intros c1 c2 step.  unfold st_heap in *. induction step; simpl in *.  
unfold domain at 2. unfold domain at 2 in IHstep. rewrite map_app. assert
(di:=@domain_inf nat). unfold domain in di. rewrite di with (m':=M). rewrite <-
map_app. repeat (rewrite <- app_assoc in IHstep). apply IHstep. apply
subset_id. apply subset_trans with (ys:=domain (Ψ ++ x' ↦ M :: Φ')). unfold
domain at 2. rewrite map_app. apply subset_comm2. simpl. apply subset_cons.
apply subset_comm2.  rewrite <- map_app. assumption. assumption. Qed. 

Lemma well_formed_heap_inf : ∀ Φ Ψ v m, isfresh (Ψ ++ Φ) v → closed_under m Φ → 
  well_formed_heap (Ψ ++ Φ) → well_formed_heap (Ψ ++ (v,m) :: Φ). 
intros. induction Ψ. split. assumption. auto. destruct a. simpl. split. 
inversion H1. unfold isfresh. unfold not. intros. unfold domain in H4. rewrite
map_app in H4. apply in_app_or in H4. destruct H4. apply H2. unfold domain.
rewrite map_app. apply in_or_app. auto. inversion H4. simpl in H5. subst. apply
H. simpl. auto. apply H2. simpl. unfold domain. rewrite map_app. apply
in_or_app. apply or_intror. auto. split. inversion H1. unfold closed_under.
unfold domain. rewrite map_app. 
apply subset_comm2. simpl. apply subset_cons. apply subset_comm2. destruct H3.
unfold closed_under in H3. rewrite <- map_app. auto. apply IHΨ. unfold isfresh.
unfold not. intros. apply H. simpl. apply or_intror. assumption. inversion H1.
destruct H3. assumption. Qed. 

Theorem well_formed_step : ∀ c1 c2, well_formed c1 → c1 ⇓ c2 → well_formed c2.
intros. induction H0. apply well_formed_app in H. apply IHstep in H. apply
well_formed_app' in H. apply well_formed_weaken_reach. assumption. assumption. apply IHstep2. 
simpl in H. destruct H. unfold closed_under in H. unfold fvs in H. rewrite
app_subset_and in H. destruct H. assert (well_formed (⟨Φ & Ψ ⟩ L)). split;
assumption. apply IHstep1 in H3. clear IHstep2 IHstep1 H. split. unfold
closed_under. simpl. apply subset_trans with (ys:=x'::remove x (fvs N)). apply
subst_subset. simpl. split. auto. inversion H3. unfold closed_under in H. unfold
fvs in H. apply subset_cons. assumption. inversion H3. apply
well_formed_heap_inf. destruct H0. assumption. apply subset_trans with
(ys:=domain Φ). assumption. apply monotonic_reachable in H0_. assumption.
assumption. Qed. 

Lemma unique_inf_eq {A B} : ∀ (Φ Φ' Ψ Ψ' : list (prod A B)) c, 
  unique (domain (Φ ++ c :: Ψ)) → 
  unique (domain (Φ' ++ c :: Ψ')) →
  Φ ++ c :: Ψ = Φ' ++ c :: Ψ' →
  Φ = Φ' ∧ Ψ = Ψ'. 
induction Φ; intros; destruct c. inversion H. subst. induction Φ'. simpl in H1.
inversion H1. subst. auto. destruct a0. simpl in H1. subst. inversion H1. subst.
inversion H0. subst. specialize (H6 (inf_indomain _ _ _ _)). inversion H6.
induction Φ'. inversion H1. subst. inversion H. subst. specialize (H4
(inf_indomain _ _ _ _)). inversion H4. inversion H1. subst. simpl in H1. 
simpl in H0. inversion H0. subst. inversion H. subst. 
specialize (IHΦ Φ' _ Ψ' _ H8 H6 H4). destruct IHΦ. subst. auto. Qed. 

(*
Lemma det_step : ∀ a b c, well_formed a → a ⇓ b → a ⇓ c → b = c. 
intros a b c wf s. generalize dependent c. induction s. assert (wfx := wf).
apply well_formed_app in wf.  intros. inversion H. subst. symmetry in H0. apply
unique_inf in H0; try (destruct wf; destruct H2; assumption). destruct H0.
destruct H1. subst. apply IHs in H3. inversion H3. apply unique_inf_eq
in H1. destruct H1. subst. reflexivity. subst. set (wf' := well_formed_step _ _
wf s). unfold well_formed in wf'. destruct wf'. destruct H2. assumption. subst.
rewrite H1 in s.  set (wf' := well_formed_step _ _ wf s). destruct wf'. destruct
H2. assumption. assumption. intros. inversion H. subst. auto. inversion 
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

Inductive reachable (h : heap) : nat → tm → Prop := 
  | rchi : ∀ x e, In x (fvs e) →  reachable h x e
  | rchtran : ∀ x y e e', reachable h x e → 
                           lookup x h = Some e' → 
                           In y (fvs e') → 
                           reachable h y e.

Lemma rchapp : ∀ h x y e e', reachable h x e → 
                              lookup x h = Some e' → 
                              reachable h y e' → 
                              reachable h y e.
intros. induction H1. apply rchtran with (x:=x) (e':=e0); assumption. apply
IHreachable in H0. apply rchtran with (x:=x0) (e':=e'). assumption.
assumption. assumption. Qed.

Lemma rchtran' : ∀ h x y e e', In x (fvs e) →
                                lookup x h = Some e' →
                                reachable h y e' →
                                reachable h y e. 
intros. induction H1. apply rchi with (h:=h) in H. apply rchtran with (x:=x)
(e':=e0). assumption. assumption. assumption. apply rchi with (h:=h) in H3.
apply rchapp with (x:=x0) (e':=e'); try auto. Qed.  

Lemma rchdestruct : ∀ h l e, reachable h l e → 
  In l (fvs e) ∨ 
  ∃ (e':tm) (x:nat), In x (fvs e) ∧ lookup x h = Some e' ∧ reachable h l e'. 
intros. prep_induction H. induction H; intros; auto; subst. destruct
IHreachable. apply or_intror. exists e', x. split; try auto. split; try
auto. apply rchi with (h:=h) in H1. assumption. destruct H2. destruct H2.
destruct H2. destruct H3. assert (cbn0 := rchtran _ _ _ _ _ H4 H0 H1). apply
or_intror. exists x0, x1; split; try auto.  Qed.  

Definition acyclic (Φ : heap) : Prop := forevery Φ (λ x, 
  match x with (l, e) => ¬ reachable Φ l e end). 

Lemma reachable_app : ∀ l Φ Ψ c, unique (domain (Ψ ++ Φ)) → 
  reachable (Φ ++ Ψ) l c → reachable (Ψ ++ Φ) l c. 
intros. induction H0. apply rchi. assumption. apply rchtran with (x:=x)
(e':=e'). assumption. rewrite lookup_app_unique. assumption. assumption.
assumption. Qed.  

(* Decidable reachability, not currently used *)
Definition reachables (h : heap) (e : tm) := 
let h' := concat (map (const h) h) in 
  (fix f l acc := match l with
  | nil => acc
  | cons (n, e) t => f t (if in_dec eq_nat_dec n acc then (fvs e ++ acc) else acc)
  end) h (fvs e).

(* reachability dependent *)
Lemma dup_irrelevent : ∀ l l' h  h' e,
  unique (domain (h ++ (l, e) :: h')) →
  reachable (h ++ (l, e) :: h') l' e →
  reachable (h ++ h') l' e.
intros. prep_induction H0. induction H0; intros; subst. apply
rchi. assumption. specialize (IHreachable l h h' H3 eq_refl). destruct
(eq_nat_dec x l). subst. rewrite lookup_inf in H. inversion H. subst. apply
rchi. assumption. assumption. apply rchtran with (x:=x) (e':=e'). assumption.
apply lookup_not_inf with (a:=e) (h0:=h) (h'0:=h') in n. rewrite <- n.
assumption. assumption. Qed.

Lemma reachable_cons : ∀ b h l e, unique (domain (b::h)) → reachable h l e → reachable (b::h)
l e. intros. induction H0. apply rchi. assumption. apply rchtran with (x:=x)
(e':=e'). assumption. unfold lookup. simpl. destruct b. simpl. destruct (beq_nat
x n) eqn:bxn. apply beq_nat_true in bxn. subst.  simpl in H. inversion H. subst. 
apply lookup_domain in H1. apply H5 in H1. inversion H1. assumption. assumption.
Qed. 

Lemma reachable_or_app : ∀ h l m n, (reachable h l m ∨ reachable h l n) → 
  reachable h l (app m n). 
intros. destruct H; induction H. apply rchi. simpl. apply in_or_app. apply
or_introl. assumption. apply rchtran with (x:=x) (e':=e'); try auto. apply
rchi. simpl. apply in_or_app. apply or_intror. assumption. apply rchtran with
(x:=x) (e':=e'); try auto. Qed. 

Lemma reachable_app_or : ∀ h l m n, reachable h l (app m n) →
  reachable h l m ∨ reachable h l n. 
intros. prep_induction H. induction H; intros; subst. simpl in H. apply in_app_or in H. destruct H.
apply or_introl. apply rchi. assumption. apply or_intror. apply rchi.
assumption. specialize (IHreachable m n eq_refl). destruct IHreachable.
apply or_introl. apply rchtran with (x:=x) (e':=e'); try auto. apply or_intror.
apply rchtran with (x:=x) (e':=e'); try auto. Qed. 

Lemma reachable_app_iff : ∀ h l m n, reachable h l m ∨ reachable h l n 
                                       ↔ reachable h l (app m n). 
split. apply reachable_or_app. apply reachable_app_or. Qed.

Lemma unreachable_app : ∀ h l m n, ¬ reachable h l (app m n) → ¬
reachable h l m ∧ ¬ reachable h l n. 
intros. split. unfold not. intros. apply or_introl with
(B:=reachable h l n) in H0. apply reachable_or_app in H0. apply H in H0.
assumption. unfold not. intros. apply or_intror with (A:=reachable h l m)in
H0. apply reachable_or_app in H0. apply H in H0. assumption. Qed. 

Definition substep 

Lemma heap_reachable_step : ∀ Φ Ψ m v l e, step (st Ψ m) (st Φ v) →
                                           lookup l Ψ = Some e →
                                           ∃ e', lookup l Φ = Some e' ∧  
                                           (e' = e ∨ step (st Φ e) (st Φ e')). 
intros. prep_induction H. induction H; intros; subst. inversion H3. inversion
H2. subst. clear H2. clear H3.  specialize (IHstep _ _ _ _ _ _ H0 eq_refl
eq_refl). destruct IHstep. destruct H1. destruct H2. subst. destruct
(eq_nat_dec l x). subst. rewrite lookup_inf.   
inversion H2. inversion H1. subst. clear H1. clear H2. rewrite
forevery_app in IHstep. destruct IHstep. simpl in H1. destruct H1. destruct H1.
destruct H1. destruct H1. rewrite forevery_app. split.  

*)
