Require Import Unicode.Utf8.
Require Import bisim db List NaryFunctions.
Require cem cbn expr expr_db_nat.
Require Import CpdtTactics.

(*Well formed configurations can be collapsed into a closed deBruijn term*)
Theorem well_formed_cbn_closed_db : ∀ c, cbn.well_formed c -> {e | expr_db_nat.closed e}.
intros. destruct c. induction (expr.fvs t). destruct H. 
induction h. destruct H. crush. assert (expr.closed t).
unfold expr.closed. apply util.subset_nil2. assumption. apply dbf. split with
(x:=t). assumption. destruct a. crush. 

apply dbf.

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

Definition subst_cbn_config (st : cbn.configuration) : expr_db_nat.expr := match st with
  | cbn.st hs e => deBruijn (subst_cbn_config' hs e)
  end.

Theorem cem_cbn_bisim : bisim state_rel cem.step cbn.step.
unfold bisim.
intros. split. 
  intros. induction H. destruct H. inversion H0. symmetry in H.
  apply app_cons_not_nil in H. inversion H.  apply ex_intro with (cbn.st nil
  (expr.abs v b)). assert (cbn.step (cbn.st nil (expr.abs v b)) (cbn.st nil
  (expr.abs v b))).  apply cbn.Abs. split. assumption. 
    apply init. with (cem.st nil (cem.close (expr_db_nat.lam b') 0))
                    (cbn.st nil (expr.abs v b)).
