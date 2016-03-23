Require cem cbn expr db relations.
Require Import Unicode.Utf8 List NaryFunctions.
Require Import expr_db util CpdtTactics.
Require Import Basics.

Definition fresh (e : list nat) (h : cem.heap):= maximum (e ++ domain h). 

(* Takes the closure from a configuration and converts it into the flattened
configuration, so its free variables are pointing directly to the correct
location*) 
Definition closure_to_expr (c : cem.configuration) : option expr.tm 
  := match c with | cem.conf h (cem.close t e') => let fix cte t e' e :=
    match t with
    | db.lam b => let f := fresh e h in 
      match cte b e' (f :: e) with
      | Some b' => Some (expr.abs f b')
      | None => None
      end
    | db.var v => match nth_error e v with
      | Some l => Some (expr.var l)
      | None => match cem.clu v e' h with
        | Some (l', _) => Some (expr.var l')
        | None => None
        end
      end
    | db.app m n => match cte m e' e with
      | Some m' => match cte n e' e with 
        | Some n' => Some (expr.app m' n')
        | None => None
        end
      | None => None
      end
    end
    in cte t e' nil
  end.


(*
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
