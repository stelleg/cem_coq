Require expr.
Require Import List Datatypes.
Require Import Arith.Peano_dec.
Require Import db util.
Require Import Unicode.Utf8. 

(* Compiles standard expressions to terms with deBruijn indices *)
Fixpoint db (t : expr.tm) (env : list nat) : option tm := match t with 
  | expr.var v => match indexofn v env with
    | Some v' => Some (var v')
    | None => None
    end
  | expr.abs v b => match db b (v::env) with 
    | Some b' => Some (lam b')
    | None => None
    end
  | expr.app m n => match db m env with
    | Some m' => match db n env with 
      | Some n' => Some (app m' n')
      | None => None
      end
    | None => None
    end
  end.

Lemma expr_closed_under_db: ∀ t xs, expr.fvs t ⊆ xs → ∃ e, db t xs = Some e. 
intros t. induction t; intros; simpl in H. destruct H. simpl. apply in_indexofn
in H. destruct H. exists x. rewrite H. auto. 

rewrite app_subset_and in H. destruct H. apply IHt1 in H. apply IHt2 in H0.
destruct H.  destruct H0. simpl. rewrite H. rewrite H0. exists (db.app x x0).
reflexivity.   

simpl in H. rewrite <- subset_remove_cons in H. apply IHt in H. destruct H.
simpl. rewrite H. exists (db.lam x). reflexivity. Qed.

Lemma expr_db_closed_under : ∀ t xs e, db t xs = Some e → expr.fvs t ⊆ xs. 
intros t. induction t; intros; simpl in H.

destruct (indexofn n xs) eqn:Heqo. apply indexofn_in in Heqo. simpl. auto.
inversion H. 

simpl. destruct (db t1 xs) eqn:Heqo. destruct (db t2 xs)
eqn:Heqo0. apply IHt1 in Heqo. apply IHt2 in Heqo0. rewrite app_subset_and; 
split; auto. inversion H. inversion H. 

specialize (IHt (n::xs)). destruct (db t (n::xs)) eqn:Heqo. inversion H. subst.
symmetry in Heqo. specialize (IHt t0 eq_refl). simpl. simpl in IHt. rewrite <-
subset_remove_cons.  assumption.  inversion H. Qed.

Lemma expr_db_closed : ∀ t e x xs, db t xs = Some e → In x (db.fvs e) → x < length xs.
intros t. induction t; intros. simpl in H. destruct (indexofn n xs) eqn:ind.
apply indexof_length in ind. inversion H. subst. simpl in H0. destruct H0.
subst. assumption. inversion H0. inversion H. simpl in H. destruct (db t1 xs)
eqn:db1. destruct (db t2 xs) eqn:db2. inversion H. subst. simpl in H0. rewrite
in_app_iff in H0. destruct H0. apply IHt1 with (x:=x) in db1; auto. apply IHt2
with (x:=x) in db2; auto. inversion H. inversion H. simpl in H. destruct (db t
(n::xs)) eqn:db. inversion H. subst. apply IHt with (x:=S x) in db. simpl in
H0. simpl in db. apply Lt.lt_S_n. assumption. simpl in H0. rewrite in_map_iff in
H0. destruct H0. destruct H0. subst. destruct x0 eqn:x0e. apply remove_in in H1.
inversion H1. simpl. simpl. assert (x0 <> 0). unfold not. intros. subst.
inversion H0. rewrite <- remove_not_in. apply H1. subst. assumption. inversion
H. Qed. 
