Require cem cbn expr db relations.
Require Import Minus.
Require Import Unicode.Utf8 List NaryFunctions.
Require Import expr_db util CpdtTactics JRWTactics.
Require Import Basics EqNat.
Require Import Compare_dec.
Require Import Arith.Peano_dec.
Import ListNotations. 

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
Definition conftolg (c:cem.closure) (h:cem.heap) (d:nat): option lgexpr := match c with
  | cem.close t e => let t' := cte t d in let fix cte' t :=
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
  | cem.close t e => forevery (db.fvs' t d) (λ x, ∃ e' c', cem.clu x e h = Some (e',c'))
  end.  

Lemma closed_to_lg : ∀ t e h d, closed_up_to (cem.close t e) h d → ∃ e', 
  conftolg (cem.close t e) h d = Some e'.
intros t. induction t; intros. unfold closed_up_to in H.  rewrite <- gfvs_fvs in
H. simpl in H. simpl. destruct (gt_dec d n). exists (lvar n).
reflexivity. simpl in H. destruct H.  destruct H. destruct H. 
rewrite H. simpl. unfold compose.  simpl. exists (gvar x). reflexivity. 

simpl. simpl in H. simpl in IHt. apply IHt in H. destruct H. exists (lam x).
rewrite H. reflexivity. auto.  

simpl. simpl in H. rewrite forevery_app in H. destruct H. apply IHt1 in H. apply
IHt2 in H0. destruct H. destruct H0. exists (app x x0). simpl in H. simpl in H0.
rewrite H; auto. rewrite H0; auto. Qed. 

Lemma wf_to_lg : ∀ c, cem.well_formed c → ∃ e, conftolg (cem.st_clos c) (cem.reachable c) 0 = Some e.
intros. destruct c. destruct H. unfold cem.closed_under in H. destruct st_clos.
rewrite db.fvs_eq_zero in H. apply closed_to_lg in H. destruct H. exists x.
apply H. Qed.

Record configuration := conf {
  st_heap : Map nat lgexpr;
  st_clos : lgexpr
}.

Lemma zero_not_in_fmap_s {a} : ∀ m, ¬ In 0 (codomain (@map (a * nat) (a * nat) (fmap S) m)). 
intros. induction m. auto. simpl. unfold not. intros. destruct H. destruct a0.
simpl in H. inversion H. apply IHm in H. inversion H. Qed. 

Lemma unique_map {a b} : ∀ m (f:a→b), relations.injective f → unique m → unique (map f m). 
intros. induction m. simpl. constructor. simpl. inversion H0. subst. apply IHm in
H4. constructor. unfold not. intros. apply H3. rewrite in_map_iff in H1.
destruct H1. destruct H1. apply H in H1. subst. assumption. assumption. Qed. 

Lemma unique_zero_fmap {a} : ∀ m (x:a), unique (codomain m) → unique (codomain ((x,0)::map (fmap S) m)). 
intros. simpl. constructor. apply zero_not_in_fmap_s. assert (codomain (map
(fmap S) m) = map S (codomain m)). induction m. reflexivity. destruct a0. simpl
in *. inversion H. subst. apply IHm in H3. rewrite H3. reflexivity. rewrite H0.
apply unique_map. unfold relations.injective. intros. apply NPeano.Nat.succ_inj.
assumption. assumption. Qed.

(* Relation for equivalent terms *)
Inductive eq_terms_rel (m:list nat) (env:nat) (h:cem.heap) iso : expr.tm → db.tm → Prop :=
  | eq_lvar : ∀ v v', indexofn v m = Some v' → 
                  eq_terms_rel m env h iso (expr.var v) (db.var v')
  | eq_gvar : ∀ v x v' cl,     x >= length m → 
                       cem.clu (x - length m) env h = Some (v',cl) →
                              In (v, v') iso →
                  eq_terms_rel m env h iso (expr.var v) (db.var x)
  | eq_abs : ∀ v b b', eq_terms_rel (v::m) env h iso b b' → 
                  eq_terms_rel m env h iso (expr.abs v b) (db.lam b')  
  | eq_app : ∀ l l' n n', eq_terms_rel m env h iso l l' → eq_terms_rel m env h iso n n' → 
                            eq_terms_rel m env h iso (expr.app l n) (db.app l' n')
.

Definition eq_terms_dec (t:expr.tm) (c:cem.closure) (h:cem.heap) : Prop := 
  Some (etolg t nil) = conftolg c h 0.

Definition eq_terms (t:expr.tm) (c:cem.closure) (h:cem.heap) iso : Prop := match c with
    cem.close e env => eq_terms_rel [] env h iso t e end.

Definition eq_heaps (h : cem.heap) (h' : cbn.heap) iso := related_lists (λ x y tl _, match x,y,tl with
  | (l, cem.cl c e), (l', t), tl => In (l, l') iso ∧ eq_terms t c tl iso
  end) h h'.

Definition eq_confs (c: cem.configuration) (c':cbn.configuration) iso : Prop := 
  cem.well_formed c ∧ cbn.well_formed c' ∧ 
  match c, c' with
  | cem.conf h ur cl, cbn.st h' ur' e' => eq_terms e' (cem.st_clos c) (cem.reachable c) iso
                                        ∧ eq_heaps (ur ++ h) (ur' ++ h') iso
                                        ∧ eq_heaps h h' iso
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

Lemma eq_terms_compile : ∀ t e xs, db t xs = Some e →
  eq_terms_rel xs 0 [] [] t e. 
induction t; intros.  simpl. simpl in H. destruct (indexofn n xs) eqn:ind. inversion
H.  subst. constructor; auto. inversion H. simpl in H.  destruct (db t1 xs)
eqn:t1e. destruct (db t2 xs) eqn:t2e. apply IHt1 in t1e. apply IHt2 in t2e.
inversion H. subst. apply eq_app; auto.  inversion H. inversion H. simpl in H.
destruct (db t (n::xs)) eqn:dbt. apply IHt in dbt. inversion H.  subst. apply
eq_abs. assumption. inversion H. Qed.

(*
Lemma expr_db_eq : ∀ t e xs, db t xs = Some e → conftolg (cem.close e 0) nil
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
 *)

Lemma expr_db_eq_confs : ∀ t e, db t nil = Some e → eq_confs (cem.I e) (cbn.I t) [].
intros. split; split. simpl. rewrite for_in_iff. intros. apply expr_db_closed
with (x:=x) in H. simpl in H. inversion H. assumption. simpl. auto. simpl.
split; auto. apply expr_db_closed_under in H. assumption. simpl. split. apply
eq_terms_compile. assumption. split; constructor. Qed.

Lemma eq_heaps_domains : ∀ h h' iso, eq_heaps h h' iso → related_lists (λ x y _ _,
  In (x, y) iso) (domain h) (domain h').
intros. induction H. constructor. simpl. destruct x. destruct c. destruct y.
simpl. destruct H. constructor; auto. assumption. Qed.

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


Lemma cons_eq_app {A} : ∀ (x:A) xs x1 x2, x :: xs = x1 ++ x2 → 
  (∃ x1', x1 = x::x1' ∧ xs = x1' ++ x2) ∨
  (x1 = nil ∧ x2 = x::xs). 
intros. destruct x1. apply or_intror. auto. apply or_introl. exists x1.
inversion H. subst. auto. Qed. 

(*
Lemma related_lists_app1 {a b} : ∀ (r:a → b → list a → list b → Prop) xs xs' ys ys', 
  related_lists r (xs ++ xs') (ys ++ ys') →
  related_lists r xs ys →
  related_lists r xs' ys'. 
intros. induction H0. assumption. simpl in H. inversion H. subst. apply
IHrelated_lists in H7. assumption. Qed. 
*)

Lemma related_lists_inj_tail {a b} : ∀ (r : a → b → list a → list b → Prop) xs x ys y, 
  related_lists r (xs ++ x :: nil) (ys ++ y :: nil) →
  r x y nil nil.
intros. prep_induction H. induction H; intros. apply app_cons_not_nil in H2.
inversion H2. destruct ys0. inversion H2. subst. destruct xs0. inversion H1.
subst. auto. inversion H1. subst. inversion H0. apply app_cons_not_nil in H4.
inversion H4. inversion H2. subst. destruct xs0. inversion H1. subst. inversion
H0. apply app_cons_not_nil in H3. inversion H3. inversion H1. subst. specialize
(IHrelated_lists xs0 x0 ys0 y0 eq_refl eq_refl). assumption. Qed.

(*
Lemma related_lists_app2 {a b} : ∀ (r:a → b → list a → list b → Prop) xs xs' ys ys', 
  related_lists r (xs ++ xs') (ys ++ ys') →
  related_lists r xs' ys' → 
  related_lists r xs ys.
intros. prep_induction H0. induction H0; intros. rewrite app_nil_r in H. rewrite app_nil_r in H.
assumption. assert (∀ a ys (y:a) ys0, ys ++ y :: ys0 = (ys ++ y :: nil) ++ ys0).
intros. rewrite <- app_assoc. reflexivity. rewrite (H2 a) in H1. rewrite (H2 b)
in H1. apply IHrelated_lists in H1.  apply related_lists_inj_tail in H1.
destruct H1. auto. Qed. 
*)

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

Lemma related_lists_in {a b} : ∀ (r: a → b → list a → list b → Prop) xs ys x,
  related_lists r xs ys →
  In x xs →
  ∃ y xs' ys', In y ys ∧ r x y xs' ys'.
intros. prep_induction H. induction H; intros. inversion H0. simpl in H1.
destruct H1. subst. exists y, xs, ys. split. simpl. auto. assumption. apply
IHrelated_lists in H1. destruct H1. destruct H1. destruct H1. destruct H1.
exists x1, x2, x3. split. simpl. auto. assumption. Qed. 

Lemma related_lists_in' {a b} : ∀ (r: a → b → list a → list b → Prop) xs ys y,
  related_lists r xs ys →
  In y ys →
  ∃ x xs' ys', In x xs ∧ r x y xs' ys'.
intros. prep_induction H. induction H; intros. inversion H0. simpl in H1.
destruct H1. subst. exists x, xs, ys. split. simpl. auto. assumption. apply
IHrelated_lists in H1. destruct H1. destruct H1. destruct H1. destruct H1.
exists x0, x1, x2. split. simpl. auto. assumption. Qed. 

Lemma unique_inf_not_in {a} : ∀ xs ys (l:a), 
  unique (xs ++ l :: ys) →
  ¬ In l xs ∧ ¬ In l ys. 
intros. apply unique_app_comm in H. simpl in H. inversion H. subst.
apply not_in_app in H2. destruct H2. auto. Qed.  

Lemma list_inj_tail {A} : ∀ xs, xs = nil ∨ ∃ (x:A) ys, xs = ys ++ [x]. 
intros. induction xs. auto. apply or_intror. destruct IHxs. subst. exists a,
nil. auto. destruct H. destruct H. rewrite H. exists x, (a::x0). reflexivity.
Qed. 

Lemma related_not_cons {a b} : ∀ r xs (ys:list b) (x:a), 
  related_lists r xs ys →
  not (related_lists r (x::xs) ys). 
intros. prep_induction H. induction H; intros. unfold not. intros. inversion H.
unfold not. intros. inversion H1. subst. apply IHrelated_lists in H7.
assumption.  Qed.

Inductive eq_length {a b} : list a → list b → Prop :=
  | el_nil : eq_length [] []
  | el_cons : ∀ xs ys x y, eq_length xs ys → eq_length (x::xs) (y::ys).

Lemma eleq {a b} : ∀ (xs : list a) (ys : list b), eq_length xs ys <-> length xs = length ys.
split; intros. induction H. auto. simpl; rewrite IHeq_length; reflexivity.
prep_induction xs. induction xs; intros. inversion H. destruct ys. constructor.
inversion H1.  prep_induction ys. induction ys; intros. inversion H. simpl in H.
inversion H. apply IHxs in H1. constructor. assumption. Qed.

Lemma related_lists_eq_length {a b} : ∀ r (xs:list a) (ys:list b), 
  related_lists r xs ys → 
  eq_length xs ys. 
intros. induction H. constructor. constructor. assumption. Qed. 

Lemma eq_length_app1 {a b} : ∀ (xs xs':list a) (ys ys':list b),
  eq_length xs ys →
  eq_length (xs ++ xs') (ys ++ ys') → 
  eq_length xs' ys'.
intros. induction H. assumption. inversion H0. subst. apply IHeq_length.
assumption. Qed. 

Lemma eq_length_comm {a} : ∀ (xs xs':list a), 
  eq_length (xs ++ xs') (xs' ++ xs). 
intros. rewrite eleq. rewrite app_length. rewrite Plus.plus_comm. rewrite <-
app_length. reflexivity. Qed. 

Lemma eq_length_app2 {a b} : ∀ (xs xs':list a) (ys ys':list b),
  eq_length xs' ys' →
  eq_length (xs ++ xs') (ys ++ ys') → 
  eq_length xs ys.
intros. rewrite eleq in H0. rewrite app_length in H0. rewrite Plus.plus_comm in
H0. rewrite app_length in H0. rewrite <- app_length in H0. rewrite
Plus.plus_comm in H0. rewrite <- app_length in H0. rewrite <- eleq in H0. apply
eq_length_app1 in H0; auto. Qed.   

Lemma related_lists_app {a b} : ∀ (r:a → b → list a → list b → Prop) xs xs' ys ys', 
  eq_length xs ys → 
  related_lists r (xs ++ xs') (ys ++ ys') → 
  related_lists r xs' ys'. 
intros. induction H. auto. apply IHeq_length. inversion H0. subst. assumption.
Qed. 

Lemma related_lists_app' {a b} : ∀ (r:a → b → list a → list b → Prop) xs xs' ys ys', 
  eq_length xs' ys' → 
  related_lists r (xs ++ xs') (ys ++ ys') → 
  related_lists r xs' ys'. 
intros. assert (H0':=H0). apply related_lists_eq_length in H0'. apply
eq_length_app2 in H0'; auto. apply related_lists_app in H0; auto. Qed.

Lemma related_lists_inf {a b} : ∀ (x:a) xs xs' (y:b) ys ys' r, 
  eq_length xs ys →
  related_lists r (xs ++ x :: xs') (ys ++ y :: ys') →
  r x y xs' ys'. 
intros. prep_induction H. induction H; intros. inversion H0. subst. assumption.
simpl in H0. inversion H0. subst. apply IHeq_length in H6. assumption. Qed. 

Lemma related_lists_inf' {a b} : ∀ (x:a) xs xs' (y:b) ys ys' r, 
  eq_length xs' ys' →
  related_lists r (xs ++ x:: xs') (ys ++ y :: ys') →
  r x y xs' ys'. 
intros. assert (H0':=H0). apply related_lists_eq_length in H0. apply
eq_length_app2 in H0.  eapply related_lists_inf. apply H0. apply H0'.
constructor. assumption. Qed.

Lemma related_lists_injtl {a b} : ∀ (x:a) xs (ys : list b) r,
  related_lists r (xs ++ [x]) ys → 
  ∃ ys' y, ys = ys' ++ [y].
intros. induce xs. inversion H. subst. inversion H4. subst. exists nil,
y. reflexivity. inversion H. subst. apply IHxs in H4. destruct H4. destruct H0.
subst. exists (y::x0), x1. reflexivity. Qed.

Lemma related_lists_injtr {a b} : ∀ (x:a) xs (ys : list b) r,
  related_lists r ys (xs ++ [x]) → 
  ∃ ys' y, ys = ys' ++ [y].
intros. induce xs. inversion H. subst. inversion H4. subst. exists nil,
x0. reflexivity. inversion H. subst. apply IHxs in H4. destruct H4. destruct H0.
subst. exists (x0::x1), x2. reflexivity. Qed.

Lemma related_lists_inf1 {a b} : ∀ (x:a) xs xs' (ys:list b) r, 
  related_lists r (xs ++ x :: xs') ys → 
  ∃ y ys' ys'', ys = ys' ++ y :: ys'' ∧ 
                related_lists r xs' ys''.
intros. induce xs.  inversion H. subst. exists y, [], ys0.
split; auto. inversion H. subst. apply IHxs in H4. destruct H4. destruct H0.
destruct H0. destruct H0. subst. exists x0, (y::x1), x2. split; auto. Qed.

Lemma related_lists_flip {a b} : ∀ (xs:list a) (ys:list b) r, related_lists r xs ys →
                                          related_lists (λ x y xs ys , r y x ys xs) ys xs. 
intros. induction H. constructor. constructor. assumption. assumption. Qed. 

Lemma related_lists_inf2 {a b} : ∀ (x:a) xs xs' (ys:list b) r, 
  related_lists r ys (xs ++ x :: xs') → 
  ∃ y ys' ys'', ys = ys' ++ y :: ys''∧ 
  related_lists (λ x y xs ys, r y x ys xs) xs' ys''. 
intros. apply related_lists_flip in H. apply related_lists_inf1 in H.
assumption. Qed. 

Lemma eq_confs_inf : ∀ x x' l m c e y y' m' c' iso, 
  eq_confs (cem.conf  y' (x' ++ [(l, cem.cl c e)]) c')
           (cbn.st y (x ++ [(l, m)]) m')
           iso
→ eq_terms m c y' iso.
intros. destruct H. destruct H0. destruct H1. destruct H2. unfold eq_heaps in
H2. rewrite <- app_assoc in H2. rewrite <- app_assoc in H2. simpl in H2. apply
related_lists_inf' in H2. destruct H2. assumption. apply related_lists_eq_length
in H3. assumption. Qed. 

Lemma eq_confs_var1 : ∀ Φ Ψ x t e ur ur' iso, 
  eq_confs (cem.conf Φ ur (cem.close t e)) 
           (cbn.st Ψ ur' (expr.var x)) 
           iso → 
  ∃ v, t = db.var v.
intros. inversion H. destruct H1. destruct H2. inversion H2. subst. exists v'.
reflexivity. subst. exists x0. reflexivity. Qed. 

Lemma eq_confs_lam1 : ∀ Φ Ψ x b t e ur ur' iso, 
  eq_confs (cem.conf Φ ur (cem.close t e)) 
           (cbn.st Ψ ur' (expr.abs x b)) 
           iso → 
  ∃ b, t = db.lam b.
intros. destruct H. destruct H0. destruct H1. inversion H1. subst. exists b'.
reflexivity.  Qed. 

Lemma eq_confs_app1 : ∀ Φ Ψ m n t e ur ur' iso,
  eq_confs (cem.conf Φ ur (cem.close t e)) 
           (cbn.st Ψ ur' (expr.app m n)) iso → 
  ∃ m n, t = db.app m n.
intros. destruct H. destruct H0. destruct H1. inversion H1. subst. exists l',
n'. reflexivity. Qed. 

Lemma map_eq_app {a b} : ∀ xs ys zs (f:a→b), map f xs = ys ++ zs → ∃ ys' zs', 
  xs = ys' ++ zs' ∧ ys = map f ys' ∧ zs = map f zs'. 
induction xs; intros. simpl in H. symmetry in H. apply app_eq_nil in H. destruct
H. subst. exists nil, nil. split. reflexivity. split; reflexivity. destruct ys.
destruct zs. inversion H. inversion H. subst. simpl in H. specialize (IHxs nil
(map f xs) f eq_refl). destruct IHxs. destruct H0. exists nil, (a0::xs). auto.
simpl in H. inversion H. subst. apply IHxs in H2. destruct H2. destruct H0.
destruct H0. destruct H1. subst. exists (a0::x), x0. auto. Qed. 

(*
Lemma eq_heaps_app1 : ∀ Φ Ψ Υ x M, eq_heaps Υ (Φ ++ (x, M) :: Ψ) → 
                            ∃ Φ' Ψ' c e, Υ = Φ' ++ (x,cem.cl c e) :: Ψ' 
                                       ∧ eq_terms M c Ψ'.
intros. unfold eq_heaps in H. apply (related_lists_inf'.  _ _ _ (x,M)) in H.
destruct H. destruct H. destruct x0. destruct c. destruct H. destruct H.
destruct H0. subst. apply in_split in H. destruct H. destruct H. exists x2, x3,
c, n0. split; auto. apply in_inf.  x0, x1,
c, n0. split; auto. apply in_inf. Qed.
*)

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

(*
Inductive cem_reachable (h : cem.heap) : nat → cem.closure → Prop := 
  | rcemi : ∀ i c l e t, cem.clu i e h = Some (l, c) → cem_reachable h l (cem.close t e)
  | rcemtran : ∀ x i c l e t l', cem.clu i x h = Some (l, c) →
                          cem_reachable h l' c → cem_reachable h l' (cem.close t e).

Definition cem_acyclic (Φ : cem.heap) : Prop := forevery Φ (λ x, 
  match x with (l, cem.cl c l') => ¬ cem_reachable Φ l c end). 


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


*)

Lemma eq_length_sym {a b} : ∀ (xs:list a) (ys:list b), eq_length xs ys →
eq_length ys xs.  intros; induction H; try constructor; auto. Qed.  

Lemma related_lists_sym {a b} : ∀ (xs : list a) (ys : list b) r, 
  related_lists r xs ys → 
  related_lists (λ x y xs ys, r y x ys xs) ys xs.
intros. induce H. constructor. constructor; auto. Qed. 

Lemma related_lists_injr1 {a b} : ∀ (xs xs': list a) (ys ys': list b) y r,
  eq_length xs (ys ++ [y]) →
  related_lists r (xs ++ xs') (ys ++ [y] ++ ys') →
  ∃ xs'' x, xs = xs'' ++ [x].
intros. induce H. symmetry in H2. apply app_eq_nil in H2. crush. destruct ys0.
subst. simpl in H2. inversion H2. subst. inversion H. subst. exists nil, x.
reflexivity. inversion H2. subst. inversion H0. subst. simpl in IHeq_length.
apply IHeq_length in H7. crush. exists (x::x0), x1. reflexivity. reflexivity.
Qed. 

Lemma related_lists_injr2 {a b} : ∀ (xs xs': list a) (ys ys': list b) y r,
  eq_length xs' ys' →
  related_lists r (xs ++ xs') (ys ++ [y] ++ ys') →
  ∃ xs'' x, xs = xs'' ++ [x].
intros. assert (H0':=H0). apply related_lists_eq_length in H0. rewrite app_assoc
in H0. apply eq_length_app2 in H0; auto. apply related_lists_injr1 in H0'; auto.
Qed.  

Lemma conftolg_iff_closed_under : ∀ c e n, (∃ l, conftolg c e n = Some l) ↔ 
  closed_up_to c e n. 
intros. destruct c. generalize dependent n. induction clos_tm; intros.  
- simpl in *.  destruct (gt_dec n0 n). simpl. split;
auto. intros. exists (lvar n). reflexivity. simpl. 
unfold compose. unfold fmap_option. destruct (cem.clu (n-n0) clos_env e)
eqn:clu. simpl. split; intros; auto. destruct H. split; auto. destruct p. exists
n2, c. reflexivity. destruct p. exists (gvar n2). reflexivity. split; intros.
destruct H. inversion H. destruct H. inversion H. inversion H1. inversion H2.
- specialize IHclos_tm with (n:=S n). simpl. rewrite <- IHclos_tm. unfold
conftolg. destruct (
 (fix cte' (t : lgexpr) : option lgexpr :=
    match t with
    | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v clos_env e
    | lvar v => Some (lvar v)
    | lam b => lam <$> cte' b
    | app m n0 => app <$> cte' m <*> cte' n0
    end) (cte clos_tm (S n))). split; intros. exists l. reflexivity. simpl.
    exists (lam l). reflexivity. split; intros; inversion H; inversion H0.
- simpl in *. specialize (IHclos_tm1 n). specialize (IHclos_tm2 n). rewrite
  forevery_app. rewrite <- IHclos_tm1. rewrite <- IHclos_tm2. 
destruct (
  (fix cte' (t : lgexpr) : option lgexpr :=
       match t with
       | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v clos_env e
       | lvar v => Some (lvar v)
       | lam b => lam <$> cte' b
       | app m n0 => app <$> cte' m <*> cte' n0
       end) (cte clos_tm1 n)). 
destruct (
    (fix cte' (t : lgexpr) : option lgexpr :=
       match t with
       | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v clos_env e
       | lvar v => Some (lvar v)
       | lam b => lam <$> cte' b
       | app m n0 => app <$> cte' m <*> cte' n0
       end) (cte clos_tm2 n)).
split; intros. split. exists l. auto. exists l0. auto. exists (app l l0). auto.
split; intros. destruct H. inversion H. destruct H. destruct H0. inversion H0.
split; intros. destruct H. inversion H. destruct H. destruct H. inversion H.
Qed.

Lemma closed_up_to_0 : ∀ t e, closed_up_to t e 0 = cem.closed_under t e. 
intros. unfold closed_up_to. unfold cem.closed_under. destruct t. rewrite
db.fvs_eq_zero. reflexivity. Qed. 

Lemma fmap_option_some {A B} : ∀ (f:A → B) x y, f <$> x = Some y → ∃ z, x = Some z. 
intros. destruct x. exists a. reflexivity. inversion H. Qed. 

Lemma seq_option_some {A B} : ∀ (f:option (A → B)) x y, 
  f <*> x = Some y → ∃ z g, x = Some z ∧ f = Some g.
intros. destruct f. destruct x. exists a, b. split; auto.  inversion H.
inversion H. Qed.

Lemma eq_clu_eq_conftolg : ∀ xs ys t n c,
  (∀ x n l cl, cem.clu x n xs = Some (l, cl) → ∃ cl', cem.clu x n ys = Some (l, cl')) →
  conftolg t xs n = Some c →
  conftolg t ys n = Some c. 
intros. unfold conftolg in *. destruct t. generalize dependent n. generalize
dependent c.  induction clos_tm; intros. simpl in *. destruct (gt_dec n0 n).
assumption. assert (H0':=H0). apply fmap_option_some in H0. destruct H0.
destruct x. rewrite H0 in H0'. inversion H0'. unfold compose in H2. simpl in H2.
subst. apply H in H0. destruct H0.  simpl. rewrite H0. unfold compose. simpl.
reflexivity. simpl in *. assert (H0':=H0). apply fmap_option_some in H0'.
destruct H0'. rewrite H1 in H0. inversion H0. subst. apply IHclos_tm in H1.
rewrite H1. assumption. simpl in *. assert (H0':=H0). apply seq_option_some in
H0. destruct H0.  destruct H0. destruct H0. apply fmap_option_some in H1.
destruct H1. rewrite H0 in H0'. rewrite H1 in H0'. apply IHclos_tm1 in H1. apply
IHclos_tm2 in H0. rewrite H1. rewrite H0. assumption. Qed. 

(* If a term is closed in an environment, it's closed in an extended environment
and therefore compiles to the same locally nameless term *)
Lemma conftolg_cons : ∀ x cl xs t c n, 
  ¬ In x (domain xs) →  
  conftolg t xs n = Some c → 
  conftolg t ((x,cl)::xs) n = Some c. 
intros. unfold conftolg in *. destruct t. generalize dependent n. generalize
dependent c. induction clos_tm; simpl; intros. destruct (gt_dec n0 n).
assumption. destruct (cem.clu (n-n0) clos_env xs) eqn:clu. destruct p. simpl in
H0. destruct cl. rewrite cem.clu_cons with (c:=(n2,c0)). assumption. assumption.
assumption. inversion H0. assert (H0':=H0). apply fmap_option_some in H0.
destruct H0. rewrite H0 in H0'. apply IHclos_tm in H0. rewrite H0. assumption.
assert (H0':=H0).  apply seq_option_some in H0.  destruct H0. destruct H0.
destruct H0. apply fmap_option_some in H1. destruct H1. rewrite H0 in H0'.
rewrite H1 in H0'. inversion H0'. subst. apply IHclos_tm1 in H1.  apply
IHclos_tm2 in H0. rewrite H1. rewrite H0. assumption. Qed.

Lemma conftolg_weaken : ∀ xs ys t c n, 
  unique (domain (xs ++ ys)) →
  conftolg t ys n = Some c →
  conftolg t (xs ++ ys) n = Some c. 
intros. induction xs. assumption. inversion H. subst. apply IHxs in H4. simpl.
destruct a. simpl in *. apply conftolg_cons; auto. Qed.  

Lemma eq_terms_cons : ∀ t c x cl h iso, 
  isfresh (domain h) x → 
  eq_terms t c h iso → 
  eq_terms t c ((x,cl)::h) iso.
intros. unfold eq_terms. destruct c. simpl in H0. induction H0. constructor;
auto. apply eq_gvar with (v':=v') (cl:=cl0); auto. destruct cl. apply cem.clu_cons; auto.
apply IHeq_terms_rel in H. clear IHeq_terms_rel. apply eq_abs.
assumption. constructor; auto. Qed.

Lemma eq_terms_app : ∀ t c e e' iso, 
  unique (domain (e' ++ e)) →
  eq_terms t c e iso → eq_terms t c (e' ++ e) iso.
intros. induction e'. assumption. destruct a. simpl in *. inversion H. subst.
apply eq_terms_cons. assumption. apply IHe'. assumption. Qed.

Lemma eq_heaps_replace : ∀ xs xs' ys ys' x c n t t' c' iso,
  eq_length xs' ys' → 
  eq_heaps (xs ++ (x, cem.cl c n) :: xs') (ys ++ (x, t) :: ys') iso →
  eq_terms t' c' xs' iso → 
  eq_heaps (xs ++ (x, cem.cl c' n) :: xs') (ys ++ (x, t') :: ys') iso.
intros. assert (H0':=H0). apply related_lists_eq_length in H0'. apply
eq_length_app2 in H0'; try (constructor; auto). induction H0'. simpl in H0.
inversion H0.  subst. clear H5. simpl. constructor; auto. inversion H0. subst.
auto. split. destruct H5. assumption. assumption. destruct x0.
inversion H0. subst. apply IHH0' in H7. destruct c0. destruct y. destruct H5.
subst. constructor; auto. split; auto. unfold eq_terms in H3. destruct c0. clear
- H3. simpl in *. remember (xs ++ (x, cem.cl c n) :: xs'). induction H3; intros; subst; (try
(constructor; assumption)). apply cem.clu_inf with (c':=c') in H0. destruct H0.
apply eq_gvar with (v':=v') (cl:=x1); auto. apply eq_abs. apply
IHeq_terms_rel. reflexivity. constructor. apply IHeq_terms_rel1; reflexivity.
apply IHeq_terms_rel2; reflexivity. Qed.

Lemma eq_confs_app_lr : ∀ m n m' n' env r r' ur ur' iso, 
  eq_confs (cem.conf r ur (cem.close (db.app m n) env))
           (cbn.st r' ur' (expr.app  m' n')) iso
  ↔ 
  eq_confs (cem.conf r ur (cem.close m env))
           (cbn.st r' ur' m') iso
  ∧
  eq_confs (cem.conf r ur (cem.close n env))
           (cbn.st r' ur' n') iso. 
split; intros. 
- destruct H. destruct H0. destruct H1. simpl in H1. destruct H.
  destruct H0. inversion H1. subst.  unfold cem.closed_under in *. simpl in H. rewrite
  forevery_app in H.  destruct H. unfold cbn.closed_under in H0. simpl in H0.
  rewrite app_subset_and in H0.  destruct H0. split. split; split; auto; try
  split; auto. split; auto. split. unfold cem.closed_under. assumption.
  assumption. split; auto. split. assumption. assumption. 
- destruct H. destruct H. destruct H0. destruct H1. destruct H3. destruct H2.
  destruct H5. split. split.  simpl. destruct H0. destruct H1. destruct H. unfold
  cem.closed_under in *. rewrite forevery_app. split; auto. destruct H.
  assumption. destruct H1. destruct H2. split. split. unfold cbn.closed_under.
  simpl. rewrite app_subset_and. split; auto. assumption. simpl. split.
  constructor; assumption. auto. Qed. 
  
(*
Lemma eq_terms_eq : ∀ m env d h e t, Some (etolg e m) = conftolg (cem.close t env) h d ↔
  eq_terms_rel m env d h e t. 
split; intros. generalize dependent h. generalize dependent env. generalize
dependent d. generalize dependent m. induction t. destruct e; intros. simpl in H. 
destruct (lookup n0 m) eqn:lum. destruct (gt_dec d n). inversion H.  subst.
apply eq_lvar; assumption. unfold compose in H. unfold fmap_option in H.
destruct (cem.clu (n - d) env h). inversion H. inversion H. destruct (gt_dec d
n). inversion H. unfold compose in H. unfold fmap_option in H. destruct (cem.clu
(n-d) env h) eqn:clund. destruct p. inversion H. subst. apply eq_gvar with
(cl:=c). assumption. apply not_gt. assumption.  assumption. inversion H. simpl
in H. destruct (gt_dec d n). inversion H. unfold fmap_option in H. destruct
(cem.clu (n-d) env h). inversion H. inversion H. simpl in H. destruct (gt_dec d
n). inversion H. unfold fmap_option in H. destruct (cem.clu (n-d) env h);
inversion H. intros. unfold conftolg in H. simpl in H. destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
       match t0 with
       | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v env h
       | lvar v => Some (lvar v)
       | lam b => lam <$> cte' b
       | app m0 n => app <$> cte' m0 <*> cte' n
       end) (cte t (S d))). inversion H. 

destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
       match t0 with
       | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v env h
       | lvar v => Some (lvar v)
       | lam b => lam <$> cte' b
       | app m0 n0 => app <$> cte' m0 <*> cte' n
       end) (cte t (S d))); destruct (lookup n m); inversion H. inversion H. 
destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
      match t0 with
      | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v env h
      | lvar v => Some (lvar v)
      | lam b => lam <$> cte' b
      | app m0 n => app <$> cte' m0 <*> cte' n
      end) (cte t (S d))); inversion H1. simpl in H.
destruct ((fix cte' (t0 : lgexpr) : option lgexpr :=
      match t0 with
      | gvar v => (gvar ∘ fst (B:=cem.closure)) <$> cem.clu v env h
      | lvar v => Some (lvar v)
      | lam b => lam <$> cte' b
      | app m0 n => app <$> cte' m0 <*> cte' n
      end) (cte t (S d))). inversion H. subst. apply eq_abs with (env':=. inversion H1. simpl in H.
       
       destr induction t; simpl in H. destruct
(gt_dec (S d) n0). destruct (lookup n m); inversion H. destruct (cem.clu (n0 - S
d) env h). destruct (lookup n m); inversion H. destruct (lookup n m); inversion
H. simpl.  unfold cem.clu in H.  inversion H.  .  apply eq_gvar with
(cl:=cem.close (db.var n) env). simpl in H. 

*)
Lemma lookup_head {a} : ∀ x (m:a) h, lookup x ((x,m)::h) = Some m. 
intros. unfold lookup. unfold find. simpl. rewrite <- beq_nat_refl. reflexivity.
Qed. 

Lemma lookup_none_not_in {a} : ∀ x (m:Map nat a), lookup x m = None ↔ ¬ In x (domain m). 
split; intros. unfold not. intros. induction m. inversion H0. inversion H0.
subst. destruct a0. simpl in *. rewrite lookup_head in H. inversion H. apply
IHm. destruct a0. unfold lookup in H. unfold find in H. simpl in H.
destruct (beq_nat x n). inversion H. assumption. assumption. induction m. auto.
destruct a0. unfold lookup. unfold find. simpl. destruct (beq_nat x n) eqn:beqn.
apply beq_nat_true in beqn. subst. simpl in H. assert False. apply H. auto.
inversion H0. apply IHm. apply beq_nat_false in beqn. simpl in H. unfold not.
intros. apply H. apply or_intror. assumption. Qed. 

Lemma lookup_head_neq {a} : ∀ x y v (m:Map nat a), x ≠ y → lookup y ((x,v)::m) = lookup y m. 
intros. unfold lookup. simpl. apply not_eq_sym in H. rewrite <-
beq_nat_false_iff in H. rewrite H. reflexivity. Qed. 

Lemma utailcod {a b} : ∀ (x:a) (d:b) m, unique (codomain ((x,d)::m)) → unique (codomain m).  
intros. inversion H; auto. Qed. 

Fixpoint take {a} (n : nat) : list a → list a := λ l, match n with
  | 0 => []
  | S n => match l with 
    | [] => []
    | x::xs => x::take n xs
    end
  end.

Fixpoint subst_bindings (env: list (nat * nat)) (t:expr.tm) : expr.tm := match t with
  | expr.var v => match lookup v env with 
    | Some v' => expr.var v'
    | None => expr.var v
    end
  | expr.abs v b => expr.abs v (subst_bindings  
      (filter (λ x, match x with (y, y') => negb (beq_nat y v) end) env) b)
  | expr.app m n => expr.app (subst_bindings env m) (subst_bindings env n)
  end.

Lemma indexofn_head : ∀ x xs, indexofn x (x::xs) = Some 0. 
intros. unfold indexofn. unfold indexof. simpl. rewrite <- beq_nat_refl.
reflexivity. Qed. 

Lemma indexofnh_none_not_in : ∀ x xs m, indexofhelper xs m (beq_nat x) = None ↔ ¬ In x xs. 
split; intros. unfold not. intros. apply in_indexofnh with (m:=m) in H0. destruct H0.
rewrite H in H0. inversion H0. generalize dependent m. induction xs. auto. apply
Decidable.not_or in H. destruct H.  unfold indexofn. unfold indexof. simpl.
apply not_eq_sym in H. rewrite <- beq_nat_false_iff in H. rewrite H.  intros.
apply IHxs. assumption. Qed. 

Lemma indexofn_none_not_in : ∀ x xs, indexofn x xs = None ↔ ¬ In x xs. 
intros. unfold indexofn. unfold indexof. rewrite indexofnh_none_not_in. split;
auto. Qed. 

Fixpoint extend_heap (m:list nat) (h:cem.heap) (b:expr.tm) : cem.heap := match m with
  | [] => h
  | e::es => extend_heap (m:list nat) (h:cem.heap) (b:expr.tm) : cem.heap  
  end. 
  
Lemma eq_terms_binding : ∀ env h b b' x c m,
  eq_terms_rel m env h b b' →
  eq_terms_rel [] f ((f, cem.cl c env)::h) (expr.subst x (expr.var f) b) b'.  
intros. remember (x::m). induce H1. simpl in H. simpl.  destruct (eq_nat_dec x
v). subst. rewrite indexofn_head in H. inversion H. subst. apply eq_gvar with
(cl:=c). subst. rewrite indexofn_none_not_in. assumption.  rewrite lookup_head
in H. inversion H. subst. apply eq_gvar with (cl:=c). rewrite
lookup_none_not_in. assumption.  constructor. rewrite minus_diag. simpl. rewrite
lookup_head. reflexivity. apply eq_lvar. rewrite lookup_head_neq in H; auto.
unfold lt in H2. inversion H0. subst. rewrite lookup_head_neq in H; auto. apply
lookup_codomain in H. inversion H3. subst.
apply H6 in H.  inversion H. subst. unfold lt. assumption. simpl. destruct (eq_nat_dec x v). 
subst. rewrite lookup_head in H. inversion H. apply eq_gvar with (cl:=cl).
rewrite lookup_head_neq in H; auto. inversion H0. subst. constructor.
constructor. subst. apply Le.le_S_n in H0. constructor. assumption. rewrite
NPeano.Nat.sub_succ_r in H1. destruct (v' - d0) eqn:min. rewrite
NPeano.Nat.sub_0_le in min. unfold ge in H0. apply Le.le_trans with (n:=S d0) in
min; auto. apply Le.le_Sn_n in min. inversion min. simpl in H1. simpl. rewrite
lookup_head. apply cem.clu_cons. assumption. assumption. simpl. destruct
(eq_nat_dec x v). subst. nversion min. subst. inversion H0. symmetry in H5. apply n_Sn in
H5. inversion H5.   . constructor. inversion H5. subst. constructor. constructor.
subst. constructor. 
rewrite lookup_head_neq in H; auto. assumption. 
unfold lookup in H1. simpl in H1. apply . rewrite H1 in H0. inversion H0. subst. apply eq_gvar with (cl:=c). rewrite lookup_head in H2. inversion H2. subst. apply eq_gvar with
(cl:=c).  rewrite
lookup_none_not_in. assumption.  rewrite domain_fmap.  assumption. constructor. simpl.
rewrite lookup_head.
reflexivity. apply not_eq_sym in n. rewrite <- beq_nat_false_iff in n.
simpl in H. unfold lookup in H. simpl in H. rewrite n in H. apply eq_gvar with
(cl:=c. assumption. inversino H3. . induce
H2. simpl in H.  
prep_induction H2. induction H2. ::map (fmap S) m). remember (S d).
induce H3. 
- simpl. destruct (eq_nat_dec x v). subst. rewrite lookup_head in H. inversion
  H. subst. exists m0, 0. split; auto. split. apply Le.le_0_n. apply eq_gvar with (cl:=c).
  rewrite lookup_none_not_in.  assumption. auto. simpl. rewrite lookup_head.
  reflexivity. unfold lookup in H. simpl in H. apply not_eq_sym in n. rewrite <-
  beq_nat_false_iff in n. rewrite n in H. exists (map (fmap S) m0), d0. split.  
  apply domain_fmap. split. auto. apply eq_lvar. assumption. 
  auto. apply eq_lvar.  induction m0. inversion H. destruct a. simpl. unfold
  lookup. simpl. simpl in
  H. destruct (beq_nat v n0). 
  assumption. destruct 
  split. 
  lookup_indoin.  auto. auto.  simpl. rewrite lookup_head. auto. unfold lookup
  in H1. simpl in H1. apply
  not_eq_sym in n. rewrite <- beq_nat_false_iff in n. rewrite n in H1. inversion
  H1. inversion H5.  
- simpl. unfold lookup in H1. destruct (eq_nat_dec x v).  subst. simpl in *.
  rewrite <- beq_nat_refl in H1. inversion H1. clear H1.  apply eq_gvar with
  (cl:=cl). auto. unfold ge in *.  apply Le.le_0_n. unfold cem.clu.  simpl.
  destruct v'; simpl; rewrite lookup_head. inversion H3. apply cem.clu_cons;
  auto. simpl in H4. rewrite <- minus_n_O in H4. assumption. 
- simpl in H2. simpl. destruct (eq_nat_dec x v). subst. simpl in *.  destruct lookup simpl in *. pply H0. . simpl in H.
  destruct (beq_nat v x)
  eqn:bevx. inversion H. rewrite beq_nat_false_iff in bevx. inversion H0. subst.
  subst. rewrite <- beq_nat_refl in H.  generalize
dependent d. induction H2;
subst. apply lookup_domain in H1. simpl in H1. destruct H1. subst.  inversion
H0. subst. inversion H3. subst. inversion H6. subst. simpl. rewrite
eq_nat_dec_refl.  apply eq_gvar with (cl:=c). auto.  auto. simpl. rewrite
lookup_head. reflexivity. subst. inversion H4. subst. rewrite lookup_head in H5.
inversion H5. inversion H1. rewrite lookup_none_not_in in H1. simpl in H1.
simpl. destruct (eq_nat_dec x v). subst. assert False. apply H1. auto. inversion
H4. apply eq_gvar with (cl:=cl). auto. apply Le.le_0_n.  rewrite 

inversion H0. subst.
simpl in H5. unfold cem.clu. simpl in H2. sert (H0':=H0). apply lookup_domain in H0'.
simpl in H0'. destruct H0'. subst. simpl. rewrite eq_nat_dec_refl. apply
eq_gvar with (cl:=c). . simpl. destruct (eq_nat_dec x v). subst.
rewrite lookup_head in H1. inversion H1. subst. destruct c. inversion H2. subst. 
apply eq_gvar with (cl:=c). rewrite lookup_none_not_in. assumption. auto. simpl.
rewrite lookup_head. reflexivity. subst. inversion H4. subst. apply eq_gvar with
(cl:=c). rewrite lookup_none_not_in. assumption. auto.subst. inversion H2. subst. inversion H4.
subst. inversion H2. subst. inversion H4.  unfold isfresh in H0. inversion H2. apply
lookup_domain.  h
unfold lookup in H0. unfold find in H0. simpl in
H0. destruct (beq_nat v x). inversion H0. subst. simpl. destruct (eq_nat_dec x
v). subst. destruct d. inversion H1. simpl. remember (expr.abs x b). remember (db.lam b'). generalize
dependent h. induction
H0. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt0. subst.
clear Heqt Heqt0. simpl. simpl in IHeq_terms_rel. apply IHeq_terms_rel.
assumption. . inversion H3.  intros; subst.  unfold eq_terms in *. simpl in *. symmetry in H0. assert (H0':=H0).
apply fmap_option_some in H0. destruct H0. rewrite H0 in H0'. inversion H0'.
subst. clear H0'. unfold cte in H0. generalize dependent x. induction b;
induction b'; simpl in *; intros. destruct (eq_nat_dec x n). subst. simpl. unfold
cem.clu. rewrite lookup_head in H0. destruct (gt_dec 1 n0). inversion H0. subst.
simpl. rewrite lookup_head. destruct m.  simpl. reflexivity. simpl in H0.
rewrite <- minus_n_O.
destruct n0. specialize (n1 (Gt.gt_Sn_O 0)). inversion n1. rewrite lookup_head.
destruct m. simpl in H0.  rewrite <- minus_n_O in H0.  n1. unfold lookup. unfold
find. rewrunfold looinv ersion H0.  unfold lookup in H0.  unfold find in H0.
simpl in H0. destruct (beq_nat n x)
eqn:bnx. apply
beq_nat_true in bnx.  subst. rewrite eq_nat_dec_refl. simpl. 

Lemma cem_closed_under_extend : ∀ b f h e c, 
  isfresh h f →
  cem.closed_under (cem.close (db.lam b) e) h →
  cem.closed_under (cem.close b f) ((f, cem.cl c e)::h).
intros. crush. rewrite for_in_iff. rewrite for_in_iff in H0. intros. destruct x.
simpl. unfold lookup. simpl.  rewrite <- beq_nat_refl.  exists f, c.
reflexivity. specialize (H0 x). rewrite in_map_iff in H0. destruct H0. exists (S
x). split; auto. rewrite remove_not_in. assumption. auto. exists x0.  simpl.
unfold lookup. simpl. rewrite <- beq_nat_refl. destruct H0. exists x1. apply
cem.clu_cons. assumption. assumption. Qed.

Lemma eq_confs_step1 : ∀ ce cb cb', eq_confs ce cb → cbn.step cb cb' → ∃ ce',
  cem.step ce ce' ∧ eq_confs ce' cb'. 
intros. prep_induction H0. induction H0; intros. 
- assert (H':=H). inversion H. destruct H2.  destruct ce. destruct H3. destruct
  H4. assert (H5':=H5). assert (cbnwf:=H2). apply related_lists_inf2 in H5.
  destruct H5.  destruct H5. destruct H5. destruct H5. subst. assert (H5:=H5').
  assert (H6':=H6). apply related_lists_eq_length in H6.  apply eq_length_sym in
  H6.  apply related_lists_inf' in H5'; auto. destruct x0.  destruct c. destruct
  H5'.  subst. assert (H1':=H1). apply cem.well_formed_inf in H1. destruct
  st_clos0.  apply eq_confs_var1 in H.  destruct H.  subst.  destruct IHstep
  with (ce:=cem.conf x2 (unreachable ++ x1 ++ [(x, cem.cl c n0)]) c). split.
  apply cem.well_formed_inf in H1'. assumption. split.  apply
  cbn.well_formed_app in H2. assumption. simpl. split. assumption. repeat
  (rewrite <- app_assoc).  split. assumption. unfold eq_heaps. apply
  related_lists_sym. assumption.  destruct H. destruct x3. destruct st_clos0.
  assert (H7':=H7). apply eq_confs_lam1 in H7. destruct H7. subst. inversion
  H7'.  destruct H9. destruct H10. destruct H11. rewrite <- app_assoc in H11.
  rewrite <- app_assoc in H11. simpl in H11. rewrite app_assoc in H11. assert
  (H11' := H11).  assert (H12':=H12). apply related_lists_eq_length in H12'.
  eapply (related_lists_injr2 unreachable0 reachable _ _ (x, M) _) in H12'.
  Focus 2.  simpl. apply H11'. crush. rewrite app_assoc in H11'. apply
  related_lists_inf' in H11'. destruct x7. destruct c0.  destruct H11'. subst.
  assert (x6 = unreachable ++ x1 ∧ c = c0 ∧ n1 = n0).  inversion H; subst;
  rewrite app_assoc in H28; apply app_inj_tail in H28; destruct H28; inversion
  H24; subst; split; try split; auto. crush. exists (cem.conf (x1 ++ (x, cem.cl
  (cem.close (db.lam x3) clos_env0) n0) :: reachable) unreachable (cem.close
  (db.lam x3) clos_env0)). split.  apply cem.Id. unfold eq_terms in H3. simpl in
  H3. rewrite <- minus_n_O in H3.  inversion H3. symmetry in H24. unfold compose
  in H24. simpl in H24.  unfold fmap_option in H24. destruct (cem.clu x0
  clos_env (x1 ++ (x, cem.cl c0 n0) :: x2)) eqn:clu. destruct p. simpl in H24.
  inversion H24. subst. apply unique_clu_clo in clu. subst. reflexivity. apply
  cem.well_formed_heap_has_unique_domain. apply cem.well_formed_heap_app with
  (Φ:=unreachable). assumption.  inversion H24. assumption. assert
  (cem.well_formed_heap (unreachable ++ x1 ++ (x, cem.cl (cem.close (db.lam x3)
  clos_env0) n0) :: reachable)). inversion H7'. destruct H9. rewrite app_assoc. 
  apply cem.well_formed_heap_replace with (c:=c0). rewrite <- app_assoc.
  assumption. assumption. split; try split; auto. inversion H7'. destruct H22.
  apply cem.closed_under_weaken. apply unique_domain_app. apply
  cem.well_formed_heap_has_unique_domain. apply cem.well_formed_heap_app with
  (Φ:=unreachable). assumption. apply cem.closed_under_cons. apply
  cem.well_formed_heap_has_unique_domain in H9. repeat (rewrite <- app_assoc in
  H9). rewrite domain_app in H9. apply cem.unique_weaken_app in H9. rewrite
  domain_app in H9. apply cem.unique_weaken_app in H9. simpl in H9. inversion
  H9. assumption. assumption. apply cbn.Id in H0. apply cbn.well_formed_step in
  H0. assumption. split; auto. split; auto. apply eq_terms_app. apply
  cem.well_formed_heap_has_unique_domain. apply cem.well_formed_heap_app in
  H9. assumption. simpl. apply eq_terms_cons. apply
  cem.well_formed_heap_has_unique_domain in H20. rewrite domain_app in H20.
  rewrite domain_app in H20. rewrite app_assoc in H20. apply unique_inf_not_in
  in H20. destruct H20. simpl in H24. assumption. assumption. split. rewrite
  app_assoc. rewrite app_assoc. apply eq_heaps_replace with (c:=c0) (t:=M).
  apply related_lists_eq_length in H12. assumption. rewrite <- app_assoc.
  rewrite <- app_assoc. assumption. assumption. apply eq_heaps_replace with
  (c:=c0) (t:=M). apply related_lists_eq_length in H12. assumption. Focus 2.
  assumption. Focus 2. apply related_lists_eq_length in H12. assumption.
	apply related_lists_eq_length in H4. apply eq_length_app2 in H4. Focus 2.
  apply related_lists_eq_length in H5. assumption. apply related_lists_app in
  H11. assumption. assumption.
- destruct ce eqn:cee. destruct st_clos0. assert (H':=H). apply eq_confs_lam1 in
  H. destruct H.  rewrite H in cee. rewrite H. exists ce. rewrite cee. split;
  auto. apply cem.Abs. rewrite H in H'. assumption. 
- assert (H0':=H0). destruct ce. destruct st_clos0. apply
  eq_confs_app1 in H0'. destruct H0'. destruct H1. subst. rewrite
  eq_confs_app_lr in H0. destruct H0. apply IHstep1 in H0. destruct H0. destruct
  H0. assert (H2':=H2). destruct x2. destruct st_clos0. apply eq_confs_lam1 in
  H2'. destruct H2'. subst. assert (unreachable0 = unreachable). inversion H0;
  auto. subst. destruct IHstep2 with (ce:=cem.conf ((x', cem.cl
  (cem.close x1 clos_env) clos_env0)::reachable0) unreachable (cem.close x2
  x')). split. split. apply cem_closed_under_extend. destruct H2. destruct H3.
  destruct H4. destruct H5. apply eq_heaps_domains in H6. unfold isfresh.
  rewrite H6. unfold not. intros. destruct H. apply x3. rewrite domain_app.
  rewrite in_app_iff. auto. destruct H2. destruct H2. assumption. destruct H2.
  destruct H2. apply cem.well_formed_heap_insert_inf. destruct H3. destruct H5.
  destruct H6. apply eq_heaps_domains in H6. unfold isfresh. rewrite H6.
  destruct H. assumption. destruct H1. destruct H1. simpl. rewrite for_in_iff.
  intros. simpl in H1. rewrite for_in_iff in H1. destruct H1 with (x:=x3).
  assumption. exists x4. destruct H8. eapply cem.clu_monotonic_reachable. apply
  cem.well_formed_heap_has_unique_domain in H6. apply H6. apply H8. apply H0.
  assumption. split. split. unfold cbn.closed_under. apply subset_trans with
  (ys:=x'::remove x (expr.fvs N)). apply expr.subst_subset. simpl. split. auto.
  destruct H2. destruct H3. destruct H3. unfold cbn.closed_under in H3. simpl in
  H3. apply subset_cons. assumption. apply cbn.well_formed_heap_inf. destruct H.
  apply x3. destruct H1. destruct H3. destruct H3. apply cbn.monotonic_reachable in
  H0_. simpl in H0_.  unfold cbn.closed_under. apply subset_trans with
  (ys:=domain Φ). assumption. assumption. destruct H2. destruct H3. destruct H3.
  assumption. simpl. split. destruct H2. destruct H3. destruct H4. simpl in H4.
  unfold eq_terms. unfold eq_terms in H4. simpl in H4. symmetry in H4. assert
  (H4':=H4). apply fmap_option_some in H4. destruct H4. rewrite H4 in H4'. simpl
  in H4'. inversion H4'. subst. simpl. assumption.  unfold isfresh. unfold not.
  intros. rewrite <- subset_eq in
  H0_. apply H  
  
  destruct  with (Ψ:=reachable). . in H0. ass
  apply well_formed_heapassumption. destruct H2. destruct H3. destruct H2. simpl
  in H2.
  rewrite for_in_iff in H2. simpl. rewrite for_in_iff. intros. destruct x3.
  simpl. unfold lookup. unfold find. simpl. rewrite <- beq_nat_refl. exists x',
  (cem.close x1 clos_env). reflexivity. specialize (H2 (S x3)). simpl in H2.
  rewrite in_map_iff in H2. simpl in H2.   simpl. simpsimpl. unfold cem.clu. unfold lookup. unfold find. simpl. 
  eq_confs_app_lr. apply IHstep1 in H0.  exists   nversion H. destruct H1.
  destruct ce.
  simpl in *. destruct H0. destruct H2.
  inversion H2. subst. apply related_lists_app'.  apply  in H4. <F3> inversion H'. destruct H25.
  destruct H26. destruct H27. assumption.  
  
  Focus 2. split; auto.  simpl. unfold
  eq_terms. simpl.  assumption. replace ((x, cem.cl (cem.close (db.lam x3)
  clos_env0) n0)::reachable) with  ([(x, cem.cl (cem.close (db.lam x3)
  clos_env0) n0)]++reachable). apply cem.closed_under_weaken.apply cem.closed_under_app. assumption. simpl. estruct H10.  apply
  cem.closed_under_weaken. apply unique_domain_app. apply
  cem.well_formed_heap_has_unique_domain. assumption.
  inversion H22. destruct p. simpl in *. subst. unfold
  compose in H22. simpl in
  H22. 
  assumption.  cem.conf exists x3'. split. unfold x3'. apply cem.Id.
  onstructor.  
  
  inversion H0. destruct H2. destruct x3. (H0':=H0). apply
  eq_confs_lam1 in H0'. destruct H0. destruct H1. destruct x3. inversion H.
  subst. destruct H. apply eq_length_sym. assumption.  assumption. rewrite <-
  app_assoc. rewrite <- app_assoc. rewrite <- app_assoc(unreachable
  apply
  related_lists_inf' in H5; auto. exists inversion H.  destruct H6. destruct H7.
  destruct st_clos0. inversion H7. apply eq_confs_var1 in H. destruct H.  subst.
  simpl in H10. rewrite <- minus_n_O in H10. Focus 1. destruct (cem.clu x4
  clos_env (x0 ++ (x, cem.cl x2 x3) :: x1)) eqn:lue. Focus 2. inversion H10.
  simpl in H10.  inversion H10. destruct p.  simpl in H10. unfold compose in
  H10.  simpl in H10.  inversion H10. subst.  clear H10 H11. assert (lue':=lue).
  apply unique_clu_clo in lue. Focus 2.
  destruct H4. destruct H4. assumption. subst. clear H4.  simpl
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
