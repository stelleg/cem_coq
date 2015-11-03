Require Import List Basics.

Fixpoint elem (n: nat) (d: list nat) : Prop := match d with
  | nil => False
  | cons m ms => n = m \/ elem n ms
  end.

Fixpoint neq_bool (n m : nat) : bool := match n,m with
  | 0,0 => true
  | 0,S m' => false
  | S _, 0 => false
  | S n', S m' => neq_bool n' m'
  end.

Fixpoint subset (l : list nat) (m: list nat) : Prop := match l with
  | nil => True
  | cons x xs => elem x m /\ subset xs m
  end.

Lemma wrap : forall A B (f:A -> B), f = fun a:A => f a. auto. Qed.  

Lemma subset_nil : forall ms, subset nil ms.
intros. simpl. apply I. Qed.

Lemma or_false : forall t:Prop, (False \/ t) -> t.
intros. intros. destruct H. inversion H. assumption. Qed.

Lemma subset_filter : forall l m f, subset m l -> subset (filter f m) l .
intros. induction m. 
  apply subset_nil. 

  simpl in H. simpl. destruct (f a). unfold subset. split. destruct H.
  assumption. destruct H. apply IHm in H0. assumption. destruct H. apply IHm in
  H0. assumption. Qed.

Lemma let_inline : forall A (b c:A) f, f (let a := b in c) -> let a := b in (f c).
auto. Qed.

Lemma subset_singleton : forall x xs y, subset (x::xs) (y::nil) -> x = y.
intros. inversion H. destruct H0. assumption. inversion H0. Qed.

Lemma neq_bool_taut : forall m, neq_bool m m = true. intro. induction m. auto.
auto. Qed.

Lemma subset_cons : forall a x, subset a nil -> subset a (x::nil). intros.
induction a. auto. inversion H. inversion H0. Qed. 

Lemma cons_subset : forall x xs ys, subset (x::xs) ys -> subset xs ys. intros.
inversion H. assumption. Qed. 

Lemma subset_filter_cons : forall a v vs, subset a (v::vs) -> subset (filter
(compose negb (neq_bool v)) a) vs. 
intros. induction a. auto. inversion H. apply IHa in H1. inversion H0. rewrite
H2.  unfold filter. unfold compose. rewrite neq_bool_taut. simpl. assumption. 
unfold filter.  destruct (compose negb (neq_bool v) a). simpl. split.
assumption. assumption. assumption. Qed.

Lemma truand : forall a:Prop, True /\ a -> a.
intros. destruct H. auto. Qed. 

Lemma app_subset : forall xs ys zs, subset (xs ++ ys) zs <-> (subset xs zs /\
 subset ys zs).
intros. 
induction xs. simpl. 
split. intros. auto. intros. destruct H. assumption. 
split; intros. 
unfold subset in H. destruct H. apply IHxs in H0. destruct H0.
split. 
unfold subset. split. assumption. assumption. assumption. 
destruct H.  
rewrite <- app_comm_cons. unfold subset. split.
unfold subset in H. destruct H. assumption. 
apply IHxs.
split. unfold subset in H. destruct H. assumption. assumption. 
Qed.

Lemma elem_cons : forall n vs, elem n vs -> exists ms ns, vs = (ms ++ (n :: ns)).
intros. induction vs. inversion H. unfold elem in H. inversion H. apply ex_intro
with nil. apply ex_intro with vs. rewrite app_nil_l. rewrite H0. reflexivity.
apply IHvs in H0. destruct H0. destruct H0. apply ex_intro with (a::x). apply
ex_intro with x0. rewrite <- app_comm_cons. rewrite H0. reflexivity. Qed. 
