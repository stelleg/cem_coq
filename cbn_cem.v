Require cem cbn expr db relations.
Require Import Minus.
Require Import Unicode.Utf8 List NaryFunctions.
Require Import expr_db util CpdtTactics JRWTactics.
Require Import Basics EqNat.
Require Import Compare_dec.
Require Import Arith.Peano_dec.

Open Scope program_scope. 

(* We define a term type with local and global variables to allow us to have an
   equality relation between the cem and cbn configurations *)

Inductive lgexpr := 
  | gvar : nat → lgexpr
  | lvar : nat → lgexpr
  | lam : lgexpr → lgexpr
  | app : lgexpr → lgexpr → lgexpr.

(* Converting an exprssion to a local-global expr (lgexpr) translates bound
variables to debruijn indices and free variables to unmodified global variable
*)
Fixpoint etolg (e : expr.tm) (env : Map nat nat) :=  match e with
  | expr.abs v b => lam (etolg b ((v, 0):: map (fmap S) env))
  | expr.app m n => app (etolg m env) (etolg n env)
  | expr.var v => match lookup v env with
    | Some v' => lvar v'
    | None => gvar v
    end
  end.
 
Fixpoint cte (t:db.tm) (d:nat) : lgexpr := match t with
  | db.lam b => lam (cte b (S d))
  | db.app m n => app (cte m d) (cte n d)
  | db.var v => if gt_dec d v then lvar v else gvar (v-d)
  end.

Fixpoint gfvs (t:lgexpr) : list nat := match t with
  | lam b => gfvs b
  | app m n => gfvs m ++ gfvs n
  | gvar v => v::nil
  | lvar v => nil
  end.

Lemma gfvs_fvs : ∀ t d, gfvs (cte t d) = db.fvs' t d.
intros t. induction t; intros. simpl. destruct (gt_dec d n). reflexivity. reflexivity.
apply IHt. simpl. rewrite IHt1. rewrite IHt2. reflexivity. Qed.

Lemma forevery_in {A} : ∀ (x:A) xs p, In x xs → forevery xs p → p x.
intros. induction xs. simpl in H. inversion H. simpl in H. destruct H. simpl in
H0. subst. destruct H0. assumption. simpl in H0. destruct H0. specialize (IHxs H
H1). assumption. Qed. 

Lemma forevery_subset {A} : ∀ xs ys (p:A→Prop), xs ⊆ ys → forevery ys p → forevery xs p.
intros. induction xs. auto. simpl. simpl in H. destruct H. apply IHxs in H1.
split. apply (forevery_in _ _ _ H H0). assumption. Qed.

Lemma cte_lu : ∀ t d v, cte t d = gvar (d-v) → In (d-v) (db.fvs' t d). 
intros. destruct t; inversion H. simpl. destruct (gt_dec d n). inversion H1. inversion
H1. rewrite H2. simpl. apply (or_introl eq_refl). Qed. 

(* Converting a debruijn term requires a full configuration, we don't change
   local variables, and traverse the cactus stack to find the final location of the
   closure corresponding to a variable and a cactus location *)
Definition conftolg (c: cem.configuration) (d:nat): option lgexpr := match c with
  | cem.conf h (cem.close t e) => let t' := cte t d in let fix cte' t :=
    match t with
    | lam b => lam <$> (cte' b) 
    | app m n => app <$> (cte' m) <*> (cte' n)
    | lvar v => Some (lvar v)
    | gvar v => (gvar ∘ @fst nat _) <$> cem.clu v e h
    end in cte' t'  
  end.

Lemma clu_some_lu : ∀ v e h x, cem.clu v e h = Some x → ∃ y, lookup e h = Some y.
intros. unfold cem.clu in H. remember (lookup e h). destruct o. exists c.
reflexivity. induction v. rewrite <- Heqo in H. inversion H. rewrite <- Heqo in
H. inversion H. Qed.

Definition closed_up_to (c:cem.closure) (h:cem.heap) (d:nat) : Prop := match c with
  | cem.close t e => forevery (db.fvs' t d) (λ x, ∃ e' c', cem.clu x e h = Some (e',c') ∧ In e' (domain h))
  end.  

Lemma closed_to_lg : ∀ t e h d, closed_up_to (cem.close t e) h d → ∃ e', 
  conftolg (cem.conf h (cem.close t e)) d = Some e'.
intros t. induction t; intros. unfold closed_up_to in H.  rewrite <- gfvs_fvs in
H. simpl in H. simpl. destruct (gt_dec d n). exists (lvar n).
reflexivity. simpl in H. destruct H.  destruct H. destruct H. destruct H. 
rewrite H. simpl. unfold compose.  simpl. exists (gvar x). reflexivity. 

simpl. simpl in H. simpl in IHt. apply IHt in H. destruct H. exists (lam x).
rewrite H. reflexivity. 

simpl. simpl in H. rewrite forevery_app in H. destruct H. apply IHt1 in H. apply
IHt2 in H0. destruct H. destruct H0. exists (app x x0). simpl in H. simpl in H0.
rewrite H. rewrite H0. reflexivity. Qed. 

Lemma wf_to_lg : ∀ c, cem.well_formed c → ∃ e, conftolg c 0 = Some e.
intros. destruct c. destruct H. unfold cem.closed_under in H. destruct st_clos.
rewrite db.fvs_eq_zero in H. apply closed_to_lg in H. assumption. Qed. 

Record configuration := conf {
  st_heap : Map nat lgexpr;
  st_clos : lgexpr
}.

Definition eq_terms (t:expr.tm) (c:cem.configuration) : Prop := 
  Some (etolg t nil) = conftolg c 0.

Definition eq_heaps (h : cem.heap) (h' : cbn.heap) := related_lists (λ x y, match x,y with
  | (l, cem.cl c e), (l', t) => l = l' ∧ eq_terms t (cem.conf h c)
  end) h h'.

Definition eq_confs (c: cem.configuration) (c':cbn.configuration) : Prop := 
  cem.well_formed c ∧ cbn.well_formed c' ∧ 
  match c, c' with
  | cem.conf h cl, cbn.st h' e' => eq_terms e' c ∧ eq_heaps h h'
  end.

Fixpoint depth_env (xs : list nat) (y : nat) := match xs with 
  | nil => y
  | x::xs => if gt_dec (x+1) y then depth_env xs (x+1) else depth_env xs y
  end.

Lemma depth_env_y : ∀ xs y, y ≤ depth_env xs y. 
intros xs. induction xs; intros. simpl. auto. simpl. destruct (gt_dec (a + 1)
y). apply Gt.gt_S_le. specialize (IHxs (a + 1)). apply Gt.le_gt_trans
with (p:=y) in IHxs; auto. apply IHxs. Qed. 

Lemma depth_env_gt : ∀ xs y, forevery xs (λ x, depth_env xs y > x). 
induction xs; intros. simpl. auto. simpl. destruct (gt_dec (a + 1) y). split.
apply Gt.le_gt_trans with (m:=a+1). apply depth_env_y. rewrite Plus.plus_comm.
simpl. auto. apply IHxs. split. apply Gt.le_gt_trans with (m:=y). apply
depth_env_y. apply not_gt in n. rewrite Plus.plus_comm in n. simpl in n. apply
Gt.le_S_gt. assumption. apply IHxs. Qed.  

Lemma depth_env_map : ∀ xs y, S (depth_env xs y) = depth_env (map S xs) (S y). 
induction xs. simpl. reflexivity. simpl. intros. destruct (gt_dec (a + 1) y).
apply Gt.gt_n_S in g. destruct (gt_dec (S (a + 1)) (S y)). apply IHxs. apply n
in g. inversion g. destruct (gt_dec (S (a+1)) (S y)). apply Gt.gt_S_n in g.
apply n in g. inversion g. apply IHxs. Qed.   

Lemma expr_db_eq : ∀ t e xs, db t xs = Some e → conftolg (cem.I e)
  (depth_env (codomain xs) 0) = Some (etolg t xs).
induction t; intros; subst. inversion H. destruct (lookup n xs) eqn:Heqo.
inversion H1. subst. unfold conftolg. simpl. rewrite Heqo. apply lookup_codomain in Heqo.
assert (depth_env (codomain xs) 0 > n0). rename xs into Xs. refine (forevery_in
 _ _ _ Heqo (depth_env_gt _ _)). destruct (gt_dec (depth_env (codomain xs) 0)
 n0). reflexivity. apply n1 in H0. inversion H0. inversion H1. inversion H.
 destruct (db t1 xs) eqn:t1e. destruct (db t2 xs) eqn:t2e. specialize (IHt1 t
 xs t1e). specialize (IHt2 t0 xs t2e). unfold conftolg. simpl. inversion H1.
 subst. simpl. unfold conftolg in IHt1. simpl in IHt1. rewrite IHt1. unfold
 conftolg in IHt2. simpl in IHt2. rewrite IHt2. simpl. reflexivity. inversion
 t2e. inversion H1. inversion H1. simpl in H. destruct (db t ((n, 0) :: map
 (fmap S) xs)) eqn:dbe. apply IHt in dbe. inversion H. subst. simpl in dbe.
 simpl. rewrite depth_env_map. unfold codomain. unfold codomain in dbe. rewrite
 map_map. rewrite map_map in dbe. rewrite map_homo with (g:=(λ x : nat * nat,
 snd (fmap S x))). rewrite dbe. simpl. reflexivity. unfold homotopy. intros.
 destruct x. simpl. reflexivity. inversion H. Qed.  

Lemma expr_db_eq_confs : ∀ t e, db t nil = Some e → eq_confs (cem.I e) (cbn.I t).
intros. split; split. simpl. apply expr_db_closed in H. apply subset_nil2 in H.
rewrite H. simpl. auto. simpl. unfold cem.well_formed_heap. simpl. split. auto.
apply unil. split. simpl. apply expr_db_closed_under in H. assumption. split.
apply unil. simpl. auto. apply expr_db_eq in H. simpl. unfold eq_terms. rewrite
<- H. simpl. split. reflexivity. apply rel_nil. Qed.  

Lemma eq_heaps_domains : ∀ h h', eq_heaps h h' → domain h = domain h'. 
intros. induction H. reflexivity. destruct x. destruct c. destruct y. destruct
H. subst. simpl. f_equal. assumption. Qed.

Lemma lu_inf' {A} : ∀ h l (c:A), lookup l h = Some c → 
  ∃ Φ Ψ, h = Φ ++ (l, c) :: Ψ.
induction h. intros. inversion H. intros. unfold lookup in H. simpl in H.
destruct (EqNat.beq_nat l (fst a)) eqn:bne. destruct a. inversion H. subst.
simpl in bne. apply beq_nat_true in bne. subst. exists nil, h.  simpl.
reflexivity. apply beq_nat_false in bne. apply IHh in H. destruct H. destruct H.
exists (a::x), x0. simpl. subst. reflexivity. Qed. 

Lemma clu_inf' : ∀ x h e l c, cem.clu x e h = Some (l, c) → 
  ∃ Φ Ψ e', h = Φ ++ (l, cem.cl c e') :: Ψ.
induction x; intros. unfold cem.clu in H. destruct (lookup e h) eqn:lue.
destruct c0. inversion H. subst. apply lu_inf' in lue. destruct lue. destruct
H0. subst. exists x, x0, n. reflexivity. inversion H. assert (h':=H). apply
clu_some_lu in h'. destruct h'. unfold cem.clu in H. rewrite H0 in H. destruct
x0. apply IHx in H. destruct H. destruct H. destruct H. subst. exists x0, x1,
x2.  reflexivity. Qed. 

Lemma related_lists_app {a b} : ∀ (r:relation a b) xs xs' ys ys', 
  related_lists r xs ys → 
  related_lists r xs' ys' → 
  related_lists r (xs ++ xs') (ys ++ ys'). 
intros. induction H. assumption. simpl. constructor; assumption. Qed.  

Lemma related_lists_app1 {a b} : ∀ (r:relation a b) xs xs' ys ys', 
  related_lists r (xs ++ xs') (ys ++ ys') →
  related_lists r xs ys →
  related_lists r xs' ys'. 
intros. induction H0. assumption. simpl in H. inversion H. subst. apply
IHrelated_lists in H7. assumption. Qed. 

Lemma cons_eq_app {A} : ∀ (x:A) xs x1 x2, x :: xs = x1 ++ x2 → 
  (∃ x1', x1 = x::x1' ∧ xs = x1' ++ x2) ∨
  (x1 = nil ∧ x2 = x::xs). 
intros. destruct x1. apply or_intror. auto. apply or_introl. exists x1.
inversion H. subst. auto. Qed. 

Lemma related_lists_inj_tail {a b} : ∀ (r : relation a b) xs x ys y, 
  related_lists r (xs ++ x :: nil) (ys ++ y :: nil) →
  related_lists r xs ys ∧ r x y.
intros. prep_induction H. induction H; intros. apply app_cons_not_nil in H2.
inversion H2. destruct ys0. inversion H2. subst. destruct xs0. inversion H1.
subst. auto. inversion H1. subst. inversion H0. apply app_cons_not_nil in H4.
inversion H4. inversion H2. subst. destruct xs0. inversion H1. subst. inversion
H0. apply app_cons_not_nil in H3. inversion H3. inversion H1. subst. specialize
(IHrelated_lists xs0 x0 ys0 y0 eq_refl eq_refl). destruct IHrelated_lists.
split; auto. constructor; auto. Qed. 

Lemma related_lists_app2 {a b} : ∀ (r:relation a b) xs xs' ys ys', 
  related_lists r (xs ++ xs') (ys ++ ys') →
  related_lists r xs' ys' → 
  related_lists r xs ys.
intros. prep_induction H0. induction H0; intros. rewrite app_nil_r in H. rewrite app_nil_r in H.
assumption. assert (∀ a ys (y:a) ys0, ys ++ y :: ys0 = (ys ++ y :: nil) ++ ys0).
intros. rewrite <- app_assoc. reflexivity. rewrite (H2 a) in H1. rewrite (H2 b)
in H1. apply IHrelated_lists in H1.  apply related_lists_inj_tail in H1.
destruct H1. auto. Qed. 

Lemma not_in_cons {a} : ∀ (x:a) y xs, ¬ In x (y::xs) ↔ y ≠ x ∧ ¬ In x xs. 
intros. split. split; unfold not; intros. apply or_introl with (B:=In x xs) in H0.
simpl in H. apply H in H0. assumption. apply or_intror with (A:=y = x) in H0.
apply H in H0. assumption. intros. unfold not; intros. destruct H. simpl in H0.
destruct H0. apply H in H0. assumption. apply H1 in H0. assumption. Qed.

Lemma not_in_app {a} : ∀ (x:a) xs ys, ¬ In x (xs ++ ys) ↔ ¬ In x xs ∧ ¬ In x ys. 
intros. split. split; unfold not; intros. apply or_introl with (B:=In x ys) in H0.
apply in_or_app in H0. apply H in H0. assumption. apply or_intror with (A:=In x
xs) in H0. apply in_or_app in H0. apply H in H0. assumption. intros. unfold not.
intros. destruct H. apply in_app_or in H0. destruct H0. auto. auto. Qed.  

Lemma unique_app {a} : ∀ (xs:list a) ys, unique (xs ++ ys) → unique xs ∧ unique ys. 
intros. induction xs. split; auto. constructor. simpl in H. inversion H. subst.
apply IHxs in H3. destruct H3. split; auto. constructor. apply not_in_app in H2.
destruct H2. assumption. assumption. Qed. 

Lemma unique_inj_last {a} : ∀ xs (x:a),¬ In x xs → unique xs → unique (xs ++ x :: nil). 
induction xs; intros. simpl. constructor. assumption.
constructor. simpl. apply not_in_cons in H. destruct H. apply IHxs in H1.
inversion H0. subst. constructor. apply not_in_app. split. assumption. simpl.
unfold not. intros. destruct H2. symmetry in H2. apply H in H2. auto. auto.
assumption. inversion H0. assumption. Qed. 

Lemma unique_app_comm {a} : ∀ (xs ys : list a), unique (xs ++ ys) → 
  unique (ys ++ xs). 
induction xs; intros. rewrite app_nil_r. auto. simpl in H. inversion H. subst.
assert (a0 :: xs = (a0 :: nil) ++ xs). reflexivity.  rewrite H0. rewrite
app_assoc. apply IHxs. rewrite app_assoc. apply unique_inj_last; assumption.
Qed. 

Lemma related_lists_in {a b} : ∀ (r: relation a b) xs ys x,
  related_lists r xs ys →
  In x xs →
  ∃ y, In y ys ∧ r x y.
intros. prep_induction H. induction H; intros. inversion H0. simpl in H1.
destruct H1. subst. exists y. split; auto. simpl. auto. apply IHrelated_lists in
H1. destruct H1. destruct H1. exists x1. split. simpl. auto. auto. Qed. 

Lemma related_lists_in' {a b} : ∀ (r: relation a b) xs ys y,
  related_lists r xs ys →
  In y ys →
  ∃ x, In x xs ∧ r x y.
intros. prep_induction H. induction H; intros. inversion H0. simpl in H1.
destruct H1. subst. exists x. split; auto. simpl. auto. apply IHrelated_lists in
H1. destruct H1. destruct H1. exists x0. split. simpl. auto. auto. Qed. 

Lemma unique_inf_not_in {a} : ∀ xs ys (l:a), 
  unique (xs ++ l :: ys) →
  ¬ In l xs ∧ ¬ In l ys. 
intros. apply unique_app_comm in H. simpl in H. inversion H. subst.
apply not_in_app in H2. destruct H2. auto. Qed.  

Lemma related_lists_inf {a b} : ∀ (r : relation a b) xs xs' ys ys' x y,
  related_lists r (xs ++ x :: xs') (ys ++ y :: ys') →
  (¬ ∃ y, In y ys ∧ r x y) ∧ (¬ ∃ y, In y ys' ∧ r x y) →
  r x y.
intros. assert (In x (xs ++ x :: xs')). apply in_inf. apply (related_lists_in _
_ _ _ H) in H1. destruct H1. destruct H1. destruct H0. apply in_app_or in H1.
destruct H1. specialize (H0 (ex_intro _ x0 (conj H1 H2))).  inversion H0.
simpl in H1. destruct H1. subst. assumption. specialize (H3 (ex_intro _ x0 (conj
H1 H2))). inversion H3. Qed. 

Lemma eq_terms_cons : ∀ xs c c' f d t, isfresh xs f → 
  conftolg (cem.conf xs c) d = Some t →
  conftolg (cem.conf ((f, c')::xs) c) d = Some t. 
destruct c. generalize dependent xs. generalize dependent clos_env. induction
clos_tm; intros. simpl. simpl in H0. destruct (gt_dec d n). assumption.
destruct (cem.clu (n-d) clos_env xs) eqn:clue. rewrite <- H0. f_equal. destruct
c'. apply cem.clu_cons; assumption. inversion H0. simpl. simpl in H0. simpl in
IHclos_tm. destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
        match t0 with
        | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v clos_env xs
        | lvar v => Some (lvar v)
        | lam b => lam <$> cte' b
        | app m n => app <$> cte' m <*> cte' n
        end) (cte clos_tm (S d))) eqn:bod. specialize (IHclos_tm clos_env xs c'
f (S d) l H bod). rewrite IHclos_tm. assumption. inversion H0. simpl. simpl in
H0. 
destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
        match t0 with
        | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v clos_env xs
        | lvar v => Some (lvar v)
        | lam b => lam <$> cte' b
        | app m n => app <$> cte' m <*> cte' n
        end) (cte clos_tm1 d)) eqn:t1e. 
destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
        match t0 with
        | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v clos_env xs
        | lvar v => Some (lvar v)
        | lam b => lam <$> cte' b
        | app m n => app <$> cte' m <*> cte' n
        end) (cte clos_tm2 d)) eqn:t2e. 
specialize (IHclos_tm1 clos_env xs c' f d l H t1e). 
specialize (IHclos_tm2 clos_env xs c' f d l0 H t2e). simpl in IHclos_tm1. simpl
in IHclos_tm2. rewrite IHclos_tm1. rewrite IHclos_tm2. assumption. inversion H0.
inversion H0. Qed.  

Lemma eq_confs_inf : ∀ x x' l m c e y y' m' c', 
  eq_confs (cem.conf (x' ++ (l, cem.cl c e) :: y') c')
           (cbn.st (x ++ (l, m) :: y) m')
→ eq_terms m (cem.conf (x' ++ (l, cem.cl c e) :: y') c).
intros. destruct H. destruct H0. destruct H1. unfold eq_heaps in H2. apply
related_lists_inf in H2. destruct H2. assumption. unfold not. split; intros;
destruct H3; destruct H3; destruct x0; destruct H4; subst; destruct H0;
destruct H4; unfold domain in H4; rewrite map_app in H4; simpl in H4; apply
unique_app_comm in H4; inversion H4; apply not_in_app in H9; destruct H9; apply
in_map with (B:=nat) (f:=@fst nat expr.tm) in H3; simpl in H3. specialize (H11
H3). inversion H11. specialize (H9 H3). inversion H9. Qed. 

Lemma eq_confs_var1 : ∀ Φ Ψ x t e, 
  eq_confs (cem.conf Φ (cem.close t e)) 
           (cbn.st Ψ (expr.var x)) → 
  ∃ v, t = db.var v.
intros. inversion H. destruct H1. destruct H2. inversion H2. destruct t. exists
n. reflexivity. inversion H5. 
destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
  match t0 with
  | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v e Φ
  | lvar v => Some (lvar v)
  | lam b => lam <$> cte' b
  | app m n => app <$> cte' m <*> cte' n
  end) (cte t 1)); inversion H6. simpl in H5. 
destruct ((fix cte' (t : lgexpr) : option lgexpr :=
  match t with
  | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v e Φ
  | lvar v => Some (lvar v)
  | lam b => lam <$> cte' b
  | app m n => app <$> cte' m <*> cte' n
  end) (cte t1 0)); 
destruct ((fix cte' (t : lgexpr) : option lgexpr :=
  match t with
  | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v e Φ
  | lvar v => Some (lvar v)
  | lam b => lam <$> cte' b
  | app m n => app <$> cte' m <*> cte' n
  end) (cte t2 0)); inversion H5. Qed.

Lemma eq_confs_lam1 : ∀ Φ Ψ x b t e, 
  eq_confs (cem.conf Φ (cem.close t e)) 
           (cbn.st Ψ (expr.abs x b)) → 
  ∃ b, t = db.lam b.
intros. inversion H. destruct H1. destruct H2. inversion H2. destruct t.
inversion H5. destruct (cem.clu (n-0) e Φ); inversion H6. 
exists t. reflexivity. simpl in H5.
destruct ((fix cte' (t : lgexpr) : option lgexpr :=
  match t with
  | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v e Φ
  | lvar v => Some (lvar v)
  | lam b => lam <$> cte' b
  | app m n => app <$> cte' m <*> cte' n
  end) (cte t1 0)); 
destruct ((fix cte' (t : lgexpr) : option lgexpr :=
  match t with
  | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v e Φ
  | lvar v => Some (lvar v)
  | lam b => lam <$> cte' b
  | app m n => app <$> cte' m <*> cte' n
  end) (cte t2 0)); inversion H5. Qed.

Lemma eq_confs_app1 : ∀ Φ Ψ m n t e, 
  eq_confs (cem.conf Φ (cem.close t e)) 
           (cbn.st Ψ (expr.app m n)) → 
  ∃ m n, t = db.app m n.
intros. inversion H. destruct H1. destruct H2. inversion H2. destruct t. 
inversion H5. destruct (cem.clu (n0-0) e Φ); inversion H6. 
simpl in H5.
destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
  match t0 with
  | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v e Φ
  | lvar v => Some (lvar v)
  | lam b => lam <$> cte' b
  | app m n => app <$> cte' m <*> cte' n
  end) (cte t 1)); inversion H5. 
exists t1, t2. reflexivity. Qed.

Lemma map_eq_app {a b} : ∀ xs ys zs (f:a→b), map f xs = ys ++ zs → ∃ ys' zs', 
  xs = ys' ++ zs' ∧ ys = map f ys' ∧ zs = map f zs'. 
induction xs; intros. simpl in H. symmetry in H. apply app_eq_nil in H. destruct
H. subst. exists nil, nil. split. reflexivity. split; reflexivity. destruct ys.
destruct zs. inversion H. inversion H. subst. simpl in H. specialize (IHxs nil
(map f xs) f eq_refl). destruct IHxs. destruct H0. exists nil, (a0::xs). auto.
simpl in H. inversion H. subst. apply IHxs in H2. destruct H2. destruct H0.
destruct H0. destruct H1. subst. exists (a0::x), x0. auto. Qed. 

Lemma eq_heaps_app1 : ∀ Φ Ψ Υ x M, eq_heaps Υ (Φ ++ (x, M) :: Ψ) → 
                            ∃ Φ' Ψ' c e, Υ = Φ' ++ (x,cem.cl c e) :: Ψ' 
                                       ∧ eq_terms M (cem.conf Υ c).
intros. unfold eq_heaps in H. apply (related_lists_in' _ _ _ (x,M)) in H.
destruct H. destruct H. destruct x0. destruct c. destruct H0. subst. apply
in_split in H. destruct H. destruct H. exists x0, x1, c, n0. split; auto. apply
in_inf. Qed.

Lemma lookup_env {A} : ∀ Φ Ψ x (v:A), unique (domain (Ψ ++ (x, v) :: Φ)) → lookup x
(Ψ ++ (x, v) :: Φ) = Some v. 
intros. set (heap:=Ψ ++ (x,v) :: Φ). assert (heap = Ψ ++ (x, v) :: Φ).
reflexivity. rewrite <- H0 in H. apply unique_domain_lookup. assumption. exists
Ψ, Φ. assumption. Qed. 

Lemma unique_clu_clo : ∀ Φ Ψ x c c' v e en, unique (domain (Ψ ++ (x, cem.cl c e) :: Φ)) → 
  cem.clu v en (Ψ ++ (x, cem.cl c e) :: Φ) = Some (x, c') → c = c'. 
induction v; intros. simpl in H0. destruct (lookup en (Ψ ++ (x, cem.cl c e) ::
Φ)) eqn:lu. destruct c0. inversion H0. subst. apply lookup_env in H. rewrite H
in lu. inversion lu. reflexivity. inversion H0. simpl in H0. destruct (lookup en
(Ψ ++ (x, cem.cl c e) :: Φ)) eqn:lue. destruct c0. apply IHv in H0. assumption.
assumption. inversion H0. Qed. 

Inductive cem_reachable (h : cem.heap) : nat → cem.closure → Prop := 
  | rcemi : ∀ i c l e t, cem.clu i e h = Some (l, c) → cem_reachable h l (cem.close t e)
  | rcemtran : ∀ x i c l e t l', cem.clu i x h = Some (l, c) →
                          cem_reachable h l' c → cem_reachable h l' (cem.close t e).

Definition cem_acyclic (Φ : cem.heap) : Prop := forevery Φ (λ x, 
  match x with (l, cem.cl c l') => ¬ cem_reachable Φ l c end). 


(*
Lemma cbn_unreachable_step : ∀ l Φ Ψ t v, unique (domain Φ) → cbn.step (cbn.st Φ
t) (cbn.st Ψ v) → In l (domain Φ) → ¬ cbn_reachable Φ l t → (¬ cbn_reachable Ψ l
v ∧ ∀ t', ¬ cbn_reachable Φ l t' → ¬ cbn_reachable Ψ l t'). 
(*Var*)
intros l Φ Ψ t v ud H. prep_induction H. induction H; simpl; intros.
specialize (IHstep l Φ0 (Υ' ++ (x, M) :: Φ') M v ud). inversion H1. inversion
H2. subst.  clear H1. clear H2. specialize (IHstep eq_refl eq_refl H0).  assert
(unique (domain (Υ' ++ (x, M) :: Φ'))). set (st1 := cbn.st (Υ ++ (x, M) :: Φ)
M).  set (st2 := cbn.st (Υ' ++ (x, M) :: Φ') (expr.abs y N)). apply
(cbn.unique_step st1 st2). assumption. assumption. destruct IHstep. unfold not.
intros. apply H3. apply rcbntran' with (x:=x) (e':=M).  simpl. auto. rewrite
lookup_inf. reflexivity. assumption. assumption. subst. split. apply (not_impl _
_ H2). intros. apply cbn_dup_irrelevent in H5. apply cbn_reachable_app.
assumption. apply cbn_reachable_cons. rewrite app_comm_cons. rewrite
unique_domain_app. assumption. apply cbn_reachable_app. rewrite
unique_domain_app in H1. inversion H1. subst.  assumption. assumption. rewrite
domain_inf with (m':=M). assumption. intros. apply H4 in H5. unfold not. intros.
clear H. clear ud. clear H4. clear H3. clear H0. clear Φ Υ. prep_induction H6; induction
H6; intros; subst. apply rcbni with (h:=Υ' ++ (x0, M) :: Φ') in H0. apply H5 in
H0. inversion H0. assert (rcb := rcbntran _ _ _ _ _ H6 H0 H1). ap 

with (q:=¬cbn_reachable (Υ' ++). . specialize (H3
(rcbntran' _ _ _ _ _ H4 H5 H2)). assumption. intros. unfold not. intros. apply cbn_reachable_app.
assumption. 
(*Lam*)
inversion H2. inversion H1. subst. subst. auto. 

(*App*)
inversion H2. inversion H3. subst. clear H2. clear H3.  specialize (IHstep1 _ _
_ _ _ ud eq_refl eq_refl H4). assert (st2u := cbn.unique_step (cbn.st Φ0 L) (cbn.st Ψ
(expr.abs x N)) ud H0). simpl in st2u.  assert (unique (domain ((x', M) :: Ψ))).
apply ucons. simpl. unfold fresh' in H.  destruct H.  assumption. assumption.
assert (In l (domain Ψ)). apply cbn.monotonic_heap in H0. rewrite <- subset_eq
in H0. apply H0 in H4. simpl in H4. assumption. assert (In l (domain ((x',M)::
Ψ))). simpl. apply or_intror.  assumption. specialize (IHstep2 l _ _ _ _ H2
eq_refl eq_refl H6). apply IHstep2. unfold not. intros.  apply
cbn_unreachable_app in H5. destruct H5.  apply IHstep1 in H5. inversion H7.
subst. simpl in H2.  inversion H2. subst.  simpl in H6. destruct H6. subst.
apply H12 in H3.  inversion H3. clear IHstep2.  clear H1. clear H3.  clear st2u.
assert (expr.fvs (expr.subst x (expr.var x') N) ⊆ (expr.fvs (expr.var x') ++
remove x (expr.fvs N))). apply expr.subst_subset.  rewrite <- subset_eq in H1.
apply H1 in H9.  apply in_app_or in H9. destruct H9.  simpl in H3. destruct H3.
subst. apply H12 in H6. inversion H6. inversion H3.  clear H1.  apply
expr.fvs_body_remove in H3.  apply rcbni with (h:=Ψ) in H3.  apply H5 in H3.
assumption. subst. unfold lookup in H10. simpl in H10. destruct
(beq_nat x0 x') eqn:bx0x. inversion H10. subst. apply beq_nat_true in bx0x.
subst. 


apply H5.
apply rcbni. simpl. apply in_or_app. apply or_introl.  apply .  rewrite <-
subset_eq
in
rmc.     expr.fvs_lam_dom.  H6. subst. apply H11 in Hsimpl in
H6. subst. destruct H6. subst. destruct H. apply x0 in
H3. inversion H3. subst. 
simpl in H3. destruct H6. subst.
destruct H.
unfold isfresh in x0. inversion H3. subst. inversion H6. subst.    
bn_dup_irrelevent with (l:=l). rewrite domain_inf with (m':=M). assumption. 

destruct
(eq_nat_dec l x); subst; clear IHstep H0 H H3; induction H1;
intros; subst. apply rcbni. assumption. apply inf_indomain. 
Focus 2. intros.
apply rcbntran with (x:=x) (e':=M). simpl. left. reflexivity. apply
unique_domain_lookup.  assumption. exists Υ, Φ. reflexivity. assumption. apply
IHstep in H3. apply not_impl with (q:=cbn_reachable (Υ' ++ (x, M) :: Φ') l
(expr.abs y N)).  assumption. intros. clear H3 IHstep. apply cbn.unique_step in
H. simpl in H.  Focus 2. simpl. assumption. apply cbn_reachable_app. apply
unique_domain_app.  assumption. apply cbn_reachable_app in H1. Focus 2. rewrite
domain_inf with (m':=M). assumption.  clear H0. clear ud. prep_induction H1.
induction H1; intros; subst. inversion H1. subst. simpl in H2.
destruct H2. subst. apply
rcbni. assumption. simpl. apply or_introl. reflexivity. inversion H1. subst. apply rcbni. assumption.
simpl. apply or_intror. assumption. subst. unfold lookup in H2. simpl in H2.
destruct (beq_nat x0 x) eqn:x0x. apply beq_nat_true in x0x. subst. inversion H2.
subst. apply rcbntran with (x:=x) (e':=expr.abs y N). assumption. rewrite
lookup_app_unique. apply lookup_env. assumption. apply unique_domain_app.
assumption. apply util.unique_app. assumption. 3 prep_induction H1.
induction H1; intros; subst. simpl in H1. destruct H1. subst. apply rcbni.
assumption. simpl. apply or_introl. reflexivity. apply rcbni. assumption. simpl.
apply or_intror. auto. prep_induction H1. induction H1; intros; subst.
apply rcbni. assumption.  rewrite domain_inf with (m':=M) in H0.  assumption.
apply cbn_reachable_app in H1. Focus 2. rewrite domain_inf with (m':=expr.abs y0
N) in H3. assumption. inversion H1. subst. simpl in H5. destruct H5. subst.
apply cbn_reachable_app. unfold domain. rewrite map_app. apply util.unique_app.
rewrite <- map_app. assumption. destruct (eq_nat_dec x y). subst. apply rcbni.
assumption. simpl. apply or_introl. reflexivity. apply lookup_not_inf with
(a:=expr.abs y0 N) in n
.   assumption.
simpl. induction ewrite unique_ induction H1. simpl in H2. destruct H2. subst. H1. subst.
simpl in H5. destruct H5. substinversion H1. subst.  apply rcbntran with (x:=x)
(e':=e'). assumption. destruct (eq_nat_dec x x0).
subst. rewrite domain_inf with (m':=expr.abs y0 N) in H3. apply lookup_env in
H3.   rewrite H3 in H0. inversion H0. subst. 
clear IHcbn_reachable. . subst. apply rcbni. destruct
(eq_nat_dec y x0).  subst.  subst. rewrite lookup_env in H0. clear
IHcbn_reachable.  inversion H0. subst.
clear H0.   
assumption. assumption. assumption. reflexivity.  reflexivity.  rewrite
domain_inf with (m':=M). assumption. assumption. simpl. assumption. apply
rcbntran with (x:=x) (e':=e'). assumption.  apply lookup_app in H0. destruct H0.
apply lookup_app. left. assumption.  destruct H0. apply lookup_app. right.
split. assumption. unfold lookup. simpl.  rewrite <- beq_nat_false_iff in n.
rewrite n. unfold lookup in H2. simpl in H2.  rewrite n in H2. assumption. apply
IHcbn_reachable with (N0:=N) (y1:=y) (Φ:=Φ) (Υ:=Υ). assumptio 
lookup_total.  . . . .   . . indomain in H0.    .  .  . . .  . apply IHstep. assumption. inversion H1. subst.  clear H1.
assert (H':= H). apply (cbn.unique_step (cbn.st (Υ ++ (x, M) :: Φ) M) (cbn.st
(Υ' ++ (x, M) :: Φ') (expr.abs y N)) ud) in H. simpl in ud. inversion H2. subst.
rewrite replace_inf in IHstep.  specialize (IHstep eq_refl eq_refl H0). assert
(¬ cbn_reachable (Υ ++ (x, M) :: Φ) l M). unfold not. intros. apply rcbntran
with (x:=x) (e:=expr.var x) in H1. apply H3 in H1. assumption. simpl. left.
reflexivity. apply unique_domain_lookup. assumption. exists Υ, Φ. reflexivity.
apply IHstep in H1. unfold not. intros. induction H4; simpl;
intros; subst. rewrite domain_inf with (m':=M) in H5. specialize (H1
(rcbni _ _ _ H4 H5)). assumption. apply IHcbn_reachable. assumption. assumption.
intros. clear H2. destruct (eq_nat_dec x x0); subst. simpl in H. rewrite
domain_inf with (m':=t) in H. apply lookup_env in H. apply (not_impl _ _ _ H1). specialize (IHcbn_reachable
H0 H3). specialize (H1 (rcbntran _ _ _ _ _ H4 H5specialize (. simpl in IHcbn_reachable. clear H6. specialize
(H7 (rcbntran _ _ _ _ _ H H0 H4)).  specialize
(IHcbn_reachable M N y x0 Φ Υ Φ' Υ' H1 ud H2 H3 H'). 
in H1. apply IHcbn_reachable in . apply IHcbn_reachable; try assumption.
intros. apply IHstep in H7. rewrite domain_inf
with (m':=M in specialize (H7
(rcbntran _ _ _ _ _ H4 H5 H6)). specialize (H3
(rcbntran _ x _ (expr.var x) _ _)). 
unfold not in H3. specialize (
not. intros. induction H1. rewrite domain_inf with (m' := M) in H4. 
inversion H3. intros.
simpl in H.  
(cbn_reachable (Υ ++ (x, M) :: Φ) l (expr.var x)). assert (


Lemma eq_confs_step1 : ∀ ce cb cb', eq_confs ce cb → cbn.step cb cb' → ∃ ce',
  cem.step ce ce' ∧ eq_confs ce' cb'. 
intros. prep_induction H0. induction H0; intros. inversion H. destruct H2.
destruct ce. destruct H3. assert (H4':=H4). apply eq_heaps_app1 in H4. destruct
H4. destruct H4.  destruct H4. destruct H4. destruct H4. subst. assert
(H1':=H1). apply cem.well_formed_inf in H1. inversion H. destruct H6. destruct
H7. destruct st_clos0. inversion H7. apply eq_confs_var1 in H. destruct H.
subst. simpl in H10. rewrite <- minus_n_O in H10. Focus 1. destruct (cem.clu x4 clos_env
(x0 ++ (x, cem.cl x2 x3) :: x1)) eqn:lue. Focus 2. inversion H10. simpl in H10.
inversion H10. destruct p. simpl in H10. unfold compose in H10. simpl in H10.
inversion H10. subst. clear H10 H11. assert (lue':=lue). apply unique_clu_clo in
lue. Focus 2. destruct H4. destruct H4. assumption. subst. clear H4.  simpl
in H7. clear H3.  clear H4'. simpl in H5.  apply cbn.well_formed_app in H2.
specialize (IHstep (cem.conf (x0 ++ (n, cem.cl c x3) :: x1) c) (conj H1 (conj H2 (conj H5
H8)))).  destruct IHstep.  destruct H. simpl in *. destruct x. destruct
st_clos0.  inversion H3. destruct H9. destruct H10. apply eq_heaps_app1 in H11.
destruct H11. destruct H11. destruct H11. destruct H11. destruct H11. subst.
assert (H3':=H3). apply eq_confs_lam1 in H3. destruct H3. subst.  exists
(cem.conf (x ++ (n, cem.cl (cem.close (db.lam x7) clos_env0) x3) :: x2)
(cem.close (db.lam x7) clos_env0)). 

assert (c = x5). inversion H5. inversion
H12. rewrite H11 in H13. destruct c eqn:ce. destruct x5 eqn:x5e.  rewrite <- x5e
in H13. rewrite <- ce in H13. destruct clos_tm. destruct clos_tm0. simpl in H13.
destruct (cem.clu (n0 - 0) clos_env2 (x ++ (n, cem.cl x5 x6):: x2)) eqn:clue1. .  (x0 destruct (cem.clu v clos_env1 (x0 ++
(n, cem.cl c x3) :: x1)) eqn:clu.  induction H12. destruct o
eqn:o'. subst.    split. Focus 1. apply cem.Id.
assumption.  assumption. unfold
eq_terms in H7. i

assumption. apply cem.Id. assumption. 
apply eq_confs_lam1 in Hdestruct st_clos0.  apply eq_confs_var1 in H. destruct H. subst.
inversion H6. destruct H7. destruct x4. destruct H8.
destruct st_clos0. apply eq_confs_lam1 in H6. destruct H6. subst. clear H5.
assert (H9':=H9). apply eq_heaps_app1 in H9. destruct H9. destruct H5. destruct
H5. destruct H5.  destruct H5. subst. clear H3. clear H6. clear H2. clear H1.
clear H4'. apply cem.well_formed_inf' in H. apply cbn.well_formed_app' in H7.
unfold eq_heaps in H4.   split. apply cem.Id. 
simpl. destruct H1'. simpl in H1. destruct H1. destruct H1. destruct H1.
destruct H1.  split. apply
cem.Id. simpl in H7.
exists cem.conf apply (related_lists_in' _ _ _ (x,M)) in H9'. destruct
H9'. destruct H1. destruct x10. destruct c. destruct H2. subst. destruct H4.
destruct H4.  destruct x0. destruct c.  destruct H5.  subst. unfold eq_terms in
H3. inversion H3. apply in_split in H4. destruct H4. destruct H4. subst. assert
(H1':=H1).  apply cem.well_formed_inf in H1.  assert (H2':=H2). apply
cbn.well_formed_app in
H2.  unfold eq_confs in IHstep at 1.  specialize (IHstep (cem.conf (x0 ++ (x,
cem.cl c n0) :: x1) c) (conj H1 (conj H2 (conj H6 H4')))). destruct IHstep.
destruct H4. destruct x2. assert (H':=H). destruct st_clos0. apply eq_confs_var1
in H'.  destruct H'. subst. assert (H5':=H5). destruct st_clos1. apply
eq_confs_lam1 in H5'.  destruct H5'.  subst.  assert (mono:=H4). apply
cem.monotonic_heap in mono.  rewrite <- subset_eq in mono.  unfold subset' in
mono. specialize (mono _ (inf_indomain _ _ _ _)). apply in_split in mono.
destruct mono. destruct H8.  simpl in H8. unfold domain in H8.  apply map_eq_app
in H8. destruct H8. destruct H8. destruct H8. destruct H9.  destruct x7.
inversion H10. inversion H10. subst. clear H10. destruct p. simpl. simpl in H4.
exists (cem.conf (x6 ++ (n,cem.cl (cem.close (db.lam x3) clos_env0) n0) :: x7)
(cem.close (db.lam x3) clos_env0)). simpl.  split. apply cem.Id. simpl in H7.
rewrite <- minus_n_O in H7. destruct (cem.clu x2 clos_env (x0 ++ (n, cem.cl c
n0) :: x1)) eqn:clue. destruct p. inversion H7. subst. apply clu_inf' in clue.
destruct clue. destruct H8. destruct H8. apply unique_inf in H8. destruct H7.
destruct H8. destruct H8. subst. inversion H8. subst. reflexivity. destruct H1.
destruct H9. assumption. inversion H7. assumption.  in H3.
inversion H3.  inversion H8. estruct (cem.clu n
clos_env st_heap0) eqn:clue. destruct p. unfold fmap_option in H2. unfold
compose in H2. simpl in H2. inversion H2. subst.
(cem.conf (x ++ (n0, cem.cl c x1) :: x0) c). split. assert (eq_confs (x ++ (n0 apply cem.Id. .   
inversion H5. subst. exists (cem.conf st_heap0 (cem.close (db.var n) clos_env)).
split. clos_env

Lemma eq_initial_confs : ∀ e : {e | expr.closed e}, eq_confs 
  (cem.I (proj1_sig (expr_closed_db e))) (cbn.I (proj1_sig e)).
intros. destruct (expr_closed_db e) eqn:Heqe. generalize dependent x. simpl.
induction e. generalize dependent p. induction x; intros; simpl; split; auto.
unfold eq_terms. inversion p. assert (p':=p). apply app_eq_nil in p'. destruct
p'. specialize (IHx1 H). specialize (IHx2 H0). unfold eq_terms. unfold
expr_closed_db in Heqe.  unfold closed_expr_db in Heqe. simpl in Heqe. 
destruct c'. specialize (IHx0_1 H). 
unfold conftolg. unfold etolg. induction t; simpl; intros. inversion H. destruct
(db t1 nil).  destruct (db t2 nil). inversion H. subst. split. unfold eq_terms.
simpl.
specialize (IHt1 t eq_refl). simpl in IHt1. unfold eq_terms in IHt1. subst; simpl. simpl in IHt1.
simpl in IHt2. destruct (2simpl. unfold eq_confs. split. induction t. inversion H. inversion H. simpl. auto. 

(* TODO : Proper relation *)
Inductive cem_cbn_rel : relation cem.configuration cbn.configuration :=
  | cc_rel : ∀ c1 c2, cem_cbn_rel c1 c2. 

Lemma cem_cbn_bisim : strong_bisim cem.configuration cbn.configuration
                                   cem.step          cbn.step
                                   cem_cbn_rel.
Admitted. 
Qed. 

Theorem cem_cbn_bisim : bisim state_rel cem.step cbn.step.
unfold bisim.
intros. split. 
  intros. induction H. destruct H. inversion H0. symmetry in H.
  apply app_cons_not_nil in H. inversion H.  apply ex_intro with (cbn.st nil
  (expr.abs v b)). assert (cbn.step (cbn.st nil (expr.abs v b)) (cbn.st nil
  (expr.abs v b))).  apply cbn.Abs. split. assumption. 
    apply init. with (cem.st nil (cem.close (db.lam b') 0))
                    (cbn.st nil (expr.abs v b)).

*)
