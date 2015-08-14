Require Import bisim db List NaryFunctions.
Require cem cbn expr expr_db_nat.

Inductive state_rel : relation cem.configuration cbn.configuration := 
  | init : forall t e,
           deBruijn t e -> 
           state_rel (cem.st nil (cem.close e 0)) (cbn.st nil t)
  | step : forall a b a' b',
           state_rel a b ->
           cem.step a a' -> 
           cbn.step b b' ->
           state_rel a' b'.

Fixpoint subst_cbn_config (st : cbn.configuration) : expr.tm := match st with
  | cbn.st vs e => match vs with
    | nil => e
    | (x,m)::hs => subst_cbn_config (cbn.st hs (cbn.subst x m e))
    end
  end.

Fixpoint subst_cem_config (st : cem.configuration) : expr_db_nat.expr := match st with
  | cem.st nil 

Theorem cem_cbn_bisim : bisim state_rel cem.step cbn.step.
unfold bisim.
intros. split. 
  intros. induction H. destruct H. inversion H0. symmetry in H.
  apply app_cons_not_nil in H. inversion H.  apply ex_intro with (cbn.st nil
  (expr.abs v b)). assert (cbn.step (cbn.st nil (expr.abs v b)) (cbn.st nil
  (expr.abs v b))).  apply cbn.Abs. split. assumption. 
    apply init. with (cem.st nil (cem.close (expr_db_nat.lam b') 0))
                    (cbn.st nil (expr.abs v b)).
