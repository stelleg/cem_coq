Require Import Unicode.Utf8.
Require Import Decidable.
Require expr.
Require Import List Datatypes util.
Require Import FunctionalExtensionality CpdtTactics. 
Require Import Arith.Peano_dec.
Require Import Program.Basics.
Set Implicit Arguments.

Inductive tm : Type := 
  | var : nat -> tm 
  | lam : tm -> tm
  | app : tm -> tm -> tm.

Inductive value : tm → Prop := 
  | val : ∀ b, value (lam b).

Fixpoint fvs (e:tm) : list nat := match e with
  | var v =>  v::nil
  | lam b =>  map pred (remove 0 (fvs b))
  | app m n => fvs m ++ fvs n
  end.

Definition closed (e:tm) := fvs e = nil.

Notation " :λ N " := (lam N) (at level 20).
Notation " M @ N " := (app M N) (at level 60). 
Coercion var : nat >-> tm.

Example term_1 : tm := lam (var 0).
Example term_2 : tm := app term_1 term_1.

(* TODO
Lemma dbClosedUnder (tm : expr.tm) (env : Map nat nat) : 
  subset (expr.fvs tm) (domain env) → exists e, db tm env = Some e.
intros. induction tm. apply subset_domain_map with (l:=(expr.fvs (expr.var n)))
(eq0:=eq_nat_dec) in H. simpl in H. simpl. destruct H. destruct H. rewrite H.
apply ex_intro with (var x). reflexivity. simpl in H. rewrite
app_subset_and in H. destruct H. apply IHtm1 in H. apply IHtm2 in H0. simpl.
destruct H, H0. rewrite H. rewrite H0. apply ex_intro with (app x
x0). reflexivity. simpl in H. simpl. rewrite <- subset_remove_cons in H. 
rewrite <- domain_fmap with (C:=nat) (f:=S) in H. 
induction (expr.fvs tm).
assert (subset nil (domain env)). apply subset_nil. apply IHtm in H0. destruct
H0. apply ex_intro with (lam x). 
*)

(*
Theorem closed_db_under : forall f t, subset (expr.fvs t) (domain f) -> exists
e, db t f e.
intros. induction t. destruct H. apply in_split in H. crush. clear H0.
apply ex_intro with (var n).
induction f. crush. induction t. inversion H. inversion H0. unfold expr.fvs
in H. apply app_subset_and in H. destruct H. crush. apply ex_intro with
(app x0 x). apply dbApp; assumption. apply ex_intro with
lam 
induction e. crush. apply in_split in H0. destruct H0. destruct H.   
induction H. crush. unfold domain. rewrite map_app. rewrite in_app_iff.
right. crush. crush. rewrite <- subset_remove_cons. rewrite domain_fmap in IHdb.
assumption. simpl. apply app_subset_and. crush. Qed. 
*)



