Require expr.
Require Import List Datatypes.
Require Import Arith.Peano_dec.
Require Import db util.
Require Import Unicode.Utf8. 

(* Compiles standard expressions to terms with deBruijn indices *)
Fixpoint db (t : expr.tm) (env : Map nat nat) : option tm := match t with 
  | expr.var v => match lookup v env with
    | Some v' => Some (var v')
    | None => None
    end
  | expr.abs v b => match db b ((v, 0):: map (fmap S) env) with 
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

