Require Import bisim db List.
Require cem cbn.

Inductive state_rel : relation cem.configuration cbn.configuration := 
  | init : forall t e,
           deBruijn t e -> 
           state_rel (cem.st nil (cem.close e 0)) (cbn.st nil t)
  | step : forall a b a' b',
           state_rel a b ->
           cem.step a a' -> 
           cbn.step b b' ->
           state_rel a' b'.

Theorem cem_cbn_bisim : bisim state_rel cem.step cbn.step.
unfold bisim.
intros. split. 
  intros. induction H0. apply IHstep in H. induction H. induction H. inversion H0. subst. 
assert app_cons_not_nil. rewrite <-
app_cons_not_nil in H. 
destruct H0. inversion H. rewrite app_cons_not_nil in H.
assert False. destruct H0. 
