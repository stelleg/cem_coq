Require Import Unicode.Utf8.
Require Import Decidable.
Require expr expr_db_nat.
Require Import List Datatypes util.
Require Import FunctionalExtensionality CpdtTactics. 
Require Import Arith.Peano_dec.
Require Import Program.Basics.
Set Implicit Arguments.

(* db.v : used to relate debruijn terms with standard terms *) 
Definition fmap' {A B C} (f : A -> C) : A * B -> C * B  := fun x => match x with
  | (a, b) => (f a, b) end. 

(* a relation between standard lambda terms and deBruijn-indexed term, note that
  standard variables are nats as well *)
Fixpoint db (tm : expr.tm) (env : Map nat nat) : option expr_db_nat.expr := match tm with 
  | expr.var v => match lookup eq_nat_dec v env with
    | Some v' => Some (expr_db_nat.var v')
    | None => None
    end
  | expr.abs v b => match db b ((v, 0):: map (fmap S) env) with 
    | Some b' => Some (expr_db_nat.lam b')
    | None => None
    end
  | expr.app m n => match db m env with
    | Some m' => match db n env with 
      | Some n' => Some (expr_db_nat.app m' n')
      | None => None
      end
    | None => None
    end
  end.

(* TODO
Lemma dbClosedUnder (tm : expr.tm) (env : Map nat nat) : 
  subset (expr.fvs tm) (domain env) → exists e, db tm env = Some e.
intros. induction tm. apply subset_domain_map with (l:=(expr.fvs (expr.var n)))
(eq0:=eq_nat_dec) in H. simpl in H. simpl. destruct H. destruct H. rewrite H.
apply ex_intro with (expr_db_nat.var x). reflexivity. simpl in H. rewrite
app_subset_and in H. destruct H. apply IHtm1 in H. apply IHtm2 in H0. simpl.
destruct H, H0. rewrite H. rewrite H0. apply ex_intro with (expr_db_nat.app x
x0). reflexivity. simpl in H. simpl. rewrite <- subset_remove_cons in H. 
rewrite <- domain_fmap with (C:=nat) (f:=S) in H. 
induction (expr.fvs tm).
assert (subset nil (domain env)). apply subset_nil. apply IHtm in H0. destruct
H0. apply ex_intro with (expr_db_nat.lam x). 
*)

Definition alpha_equiv (t1 t2 : expr.tm) : Prop := db t1 = db t2.

(*
Theorem closed_db_under : forall f t, subset (expr.fvs t) (domain f) -> exists
e, db t f e.
intros. induction t. destruct H. apply in_split in H. crush. clear H0.
apply ex_intro with (expr_db_nat.var n).
induction f. crush. induction t. inversion H. inversion H0. unfold expr.fvs
in H. apply app_subset_and in H. destruct H. crush. apply ex_intro with
(expr_db_nat.app x0 x). apply dbApp; assumption. apply ex_intro with
expr_db_nat.lam 
induction e. crush. apply in_split in H0. destruct H0. destruct H.   
induction H. crush. unfold domain. rewrite map_app. rewrite in_app_iff.
right. crush. crush. rewrite <- subset_remove_cons. rewrite domain_fmap in IHdb.
assumption. simpl. apply app_subset_and. crush. Qed. 
*)



