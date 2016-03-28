Require cem cbn expr db relations.
Require Import Unicode.Utf8 List NaryFunctions.
Require Import expr_db util CpdtTactics.
Require Import Basics.
Require Import Compare_dec.

Definition fresh (e : list nat) (h : cem.heap):= maximum (e ++ domain h). 

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
  | expr.abs v b => etolg b ((v, 0):: map (fmap S) env)
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

(* Converting a debruijn term requires a full configuration, we don't change
   local variables, and traverse the cactus stack to find the final location of the
   closure corresponding to a variable and a cactus location *)
Definition conftolg : cem.configuration → option lgexpr := λ c, match c with 
  | cem.conf h (cem.close t e) => let fix cte t dep :=
    match t with
    | db.lam b => lam <$> cte b (S dep)
    | db.app m n => app <$> cte m dep <*> cte n dep
    | db.var v => if gt_dec dep v 
      then Some (lvar v)
      else (λ x, gvar (fst x)) <$> cem.clu (dep - v) e h
    end in cte t 0
  end.

(*
Lemma wf_conftolg : ∀ c, cem.well_formed c → ∃ e, conftolg c = Some e.
intros. destruct c. destruct st_clos. generalize dependent clos_env. generalize
dependent st_heap. induction clos_tm; intros.  simpl. simpl in H.
destruct H. destruct H. destruct H. destruct H. destruct H. exists (gvar
clos_env).  remember (lookup clos_env st_heap). destruct o. destruct c. simpl.
reflexivity. unfold cem.clu in H. induction n. rewrite <- Heqo in H. inversion
H.  rewrite <- Heqo in H. inversion H. simpl in H. destruct H.
remember (db.fvs clos_tm). induction l. assert (map pred (remove 0 nil) = nil).
reflexivity. rewrite H1 in H. rewrite Heql in H. specialize (IHclos_tm st_heap
clos_env (conj H H0)). simpl. destruct IHclos_tm. simpl in H2. rewrite H2.   simpl in H. apply IHclos_tm. 
Definition wf_closure_to_expr : {c | cem.well_formed c} → expr.tm := match 

Definition flatten (c: {c | cem.well_formed c}) : cbn.configuration := match c with
  | exist (cem.conf h c) p => cbn.st (map (fmap (closure_to_expr ∘ cem.conf h ∘ cem.clclose) h))
                         (closure_to_expr nil h c)
  end.

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
