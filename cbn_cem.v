Require cem cbn expr db relations.
Require Import Minus.
Require Import Unicode.Utf8 List NaryFunctions.
Require Import expr_db util CpdtTactics.
Require Import Basics EqNat.
Require Import Compare_dec.

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
 
Definition fmap_option {a b} : (a → b) → option a → option b := λ f o, 
  match o with 
  | Some m => Some (f m)
  | None => None
  end.

Definition seq_option {a b} : option (a → b) → option a → option b := λ f o,
  match f, o with
    | Some g, Some a => Some (g a)
    | _, _ => None
  end.
  
Notation "f <$> x" := (fmap_option f x) (at level 30).
Notation "f <*> x" := (seq_option f x) (at level 40).

Fixpoint cte (t:db.tm) (d:nat) : lgexpr := match t with
  | db.lam b => lam (cte b (S d))
  | db.app m n => app (cte m d) (cte n d)
  | db.var v => if gt_dec d v then lvar v else gvar (v-d)
  end.

Fixpoint fvs' (t:db.tm) (d:nat) : list nat := match t with
  | db.lam b => fvs' b (S d)
  | db.app m n => fvs' m d ++ fvs' n d
  | db.var v => if gt_dec d v then nil else (v-d)::nil
  end.

Lemma filter_app {A} : ∀ xs ys (p:A → bool), filter p xs ++ filter p ys = filter p (xs ++ ys). 
intros. induction xs. reflexivity. simpl. destruct (p a). simpl. 
rewrite <- IHxs. reflexivity. apply IHxs. Qed. 

Lemma fvs_eq : ∀ t d, map (λ x, x - d) (filter (λ x, if gt_dec d x then false
else true) (db.fvs t)) = fvs' t d.
intros t. induction t; intros. simpl. destruct (gt_dec d n). reflexivity. simpl.
reflexivity. simpl. assert (∀ xs d, map (λ x : nat, x - S d) (filter (λ x : nat, if gt_dec
(S d) x then false else true) xs) = map (λ x :
nat, x - d) (filter (λ x : nat, if gt_dec d x then false else true) (map pred
(remove 0 xs)))). intros. induction xs. reflexivity. destruct a. simpl. apply
IHxs. simpl. destruct (gt_dec d0 a). apply Gt.gt_n_S in g. destruct (gt_dec (S
d0) (S a)). apply IHxs. apply n in g. inversion g. destruct (gt_dec (S d0) (S
a)). apply Gt.gt_S_n in g. apply n in g. inversion g. simpl. rewrite IHxs.
reflexivity. specialize IHt with (S d). rewrite <- IHt. rewrite H. reflexivity.
simpl. rewrite <- IHt1. rewrite <- IHt2. rewrite <- map_app. rewrite <-
filter_app. reflexivity. Qed. 

Lemma fvs_eq_zero : ∀ t, db.fvs t = fvs' t 0.
intros. rewrite <- fvs_eq. simpl. induction (db.fvs t). simpl. reflexivity. 
simpl. rewrite <- minus_n_O. rewrite <- IHl. reflexivity. Qed. 

Fixpoint gfvs (t:lgexpr) : list nat := match t with
  | lam b => gfvs b
  | app m n => gfvs m ++ gfvs n
  | gvar v => v::nil
  | lvar v => nil
  end.

Lemma gfvs_fvs : ∀ t d, gfvs (cte t d) = fvs' t d.
intros t. induction t; intros. simpl. destruct (gt_dec d n). reflexivity. reflexivity.
apply IHt. simpl. rewrite IHt1. rewrite IHt2. reflexivity. Qed.

Lemma forevery_in {A} : ∀ (x:A) xs p, In x xs → forevery xs p → p x.
intros. induction xs. simpl in H. inversion H. simpl in H. destruct H. simpl in
H0. subst. destruct H0. assumption. simpl in H0. destruct H0. specialize (IHxs H
H1). assumption. Qed. 

Lemma forevery_subset {A} : ∀ xs ys (p:A→Prop), xs ⊆ ys → forevery ys p → forevery xs p.
intros. induction xs. auto. simpl. simpl in H. destruct H. apply IHxs in H1.
split. apply (forevery_in _ _ _ H H0). assumption. Qed.

Lemma cte_lu : ∀ t d v, cte t d = gvar (d-v) → In (d-v) (fvs' t d). 
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
  | cem.close t e => forevery (fvs' t d) (λ x, ∃ e' c', cem.clu x e h = Some (e',c') ∧ In e' (domain h))
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
rewrite fvs_eq_zero in H. apply closed_to_lg in H. assumption. Qed. 

Record configuration := conf {
  st_heap : Map nat lgexpr;
  st_clos : lgexpr
}.

Definition eq_terms (t:expr.tm) (c:cem.configuration) : Prop := 
  Some (etolg t nil) = conftolg c 0.

Definition equal_heaps (h : cem.heap) (h' : cbn.heap) := related_lists (λ x y, match x,y with
  | (l, cem.cl c e), (l', t) => l = l' ∧ eq_terms t (cem.conf h c)
  end) h h'.

Definition eq_confs (c: cem.configuration) (c':cbn.configuration) : Prop := 
  cem.well_formed c ∧ cbn.well_formed c' ∧ 
  match c, c' with
  | cem.conf h cl, cbn.st h' e' => eq_terms e' c ∧ equal_heaps h h'
  end.

Lemma expr_closed_under_db: ∀ t xs, expr.fvs t ⊆ domain xs → {e | db t xs = Some e}.
intros t. induction t; intros; simpl in H. destruct H. simpl.
apply in_domain_lookup in H.  destruct H. rewrite e. exists (db.var x).
reflexivity. 

rewrite app_subset_and in H. destruct H. apply IHt1 in H. apply IHt2 in H0.
destruct H.  destruct H0. simpl. rewrite e. rewrite e0. exists (db.app x x0).
reflexivity.   

simpl in H. rewrite <- subset_remove_cons in H. rewrite <- domain_fmap with
(f:=S) in H.  specialize (IHt ((n,0)::map (fmap S) (xs))). simpl in IHt.  apply
IHt in H. simpl. destruct H. rewrite e. exists (db.lam x). reflexivity. Qed.

Lemma expr_db_closed_under : ∀ t xs e, db t xs = Some e → expr.fvs t ⊆ domain xs. 
intros t. induction t; intros; simpl in H.

destruct (lookup n xs) eqn:Heqo. apply lookup_domain in Heqo. simpl. split;
auto. inversion H. 

simpl. destruct (db t1 xs) eqn:Heqo. destruct (db t2 xs)
eqn:Heqo0. apply IHt1 in Heqo. apply IHt2 in Heqo0. rewrite app_subset_and; 
split; auto. inversion H. inversion H. 

specialize (IHt ((n,0)::map (fmap S) xs)). destruct (db t ((n,0)::map (fmap S)
xs)) eqn:Heqo. inversion H. subst. symmetry in Heqo. specialize (IHt t0
eq_refl). simpl. simpl in IHt. rewrite domain_fmap in IHt. rewrite <-
subset_remove_cons.  assumption.  inversion H. Qed.

Lemma expr_db_closed : ∀ t e xs, db t xs = Some e → db.fvs e ⊆ codomain xs. 
intros t. induction t; intros. inversion H. destruct (lookup n xs). inversion
H1. subst. simpl. split; auto. unfold codomain. inversion H. remember (lookup n
xs). destruct o. symmetry in Heqo. apply lookup_codomain in Heqo. inversion H2.
subst. assumption. inversion H2. inversion H1. simpl in H. remember (db t1 xs).
remember (db t2 xs). destruct o. destruct o0. symmetry in Heqo. symmetry in
Heqo0. apply IHt1 in Heqo. apply IHt2 in Heqo0. inversion H. subst. simpl.
rewrite app_subset_and. split; auto. inversion H. inversion H. inversion H.
remember (db t ((n,0) :: map (fmap S) xs)). destruct o. symmetry in Heqo. apply
IHt in Heqo. inversion H1. subst. simpl. simpl in Heqo. unfold codomain in Heqo.
rewrite map_map in Heqo. rewrite subset_remove_cons in Heqo. apply subset_map with
(f:=pred) in Heqo. rewrite map_map in Heqo. simpl. rewrite (map_homo _ _
snd_fmap) in Heqo. assumption. inversion H1. Qed. 

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

Lemma equal_heaps_domains : ∀ h h', equal_heaps h h' → domain h = domain h'. 
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

Lemma eq_confs_step1 : ∀ ce cb cb', eq_confs ce cb → cbn.step cb cb' → ∃ ce',
  cem.step ce ce' ∧ eq_confs ce' cb'. 
intros. generalize dependent ce. induction H0; intros; subst. destruct H.
destruct H1. destruct ce. destruct H2. unfold eq_terms in H2. simpl in H2.
destruct st_clos0. destruct clos_tm. simpl in H2. destruct (cem.clu (n - 0)
clos_env st_heap0) eqn:clue. destruct p. unfold fmap_option in H2. unfold
compose in H2. simpl in H2. inversion H2. subst. assert (infe:=clue). apply
clu_inf' in infe. destruct infe. destruct H4. destruct H4. subst. specialize
(IHstep (cem.conf (x ++ (n0, cem.cl c x1) :: x0) c)). exists
(cem.conf (x ++ (n0, cem.cl c x1) :: x0) c). split. apply cem.Id. .   
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

(*Well formed configurations can be collapsed into a closed deBruijn term*)
Theorem well_formed_cbn_closed_db : ∃ c, cbn.well_formed c ↔ ∃ e, db.closed e.
intros. destruct c. induction (expr.fvs t). destruct H. 
induction h. destruct H. crush. assert (expr.closed t).
unfold expr.closed. apply util.subset_nil2. assumption. apply dbf. split with
(x:=t). assumption. destruct a. crush. 

(* Relation idea: replace deBruijn variable with lookup location, which makes
them equal *)

Inductive state_rel : relation cem.configuration cbn.configuration := 
  | init : forall t e,
           deBruijn t e -> 
           state_rel (cem.st nil (cem.close e 0)) (cbn.st nil t)
  | step : forall a b a' b',
           state_rel a b ->
           cem.step a a' -> 
           cbn.step b b' ->
           state_rel a' b'.

Lemma ex1 : state_rel (cem.abs (0) 

Fixpoint subst_cbn_config' vs e : expr.tm := match vs with
  | nil => e
  | (x,m)::hs => subst_cbn_config' hs (cbn.subst x m e)
  end.

Definition subst_cbn_config (st : cbn.configuration) : db.expr := match st with
  | cbn.st hs e => deBruijn (subst_cbn_config' hs e)
  end.

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
