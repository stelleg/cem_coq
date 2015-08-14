Require Import List.

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

Lemma let_inline : forall a b c f, f (let a := b in c) -> let a := b in (f c).
