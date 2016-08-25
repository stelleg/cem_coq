Require Import FSets.FSetInterface util EqNat Sumbool Decidable.
Require Import Arith.Peano_dec.
Require Import CpdtTactics.

Inductive tm : Type :=
  | var : nat -> tm
  | app : tm -> tm -> tm
  | abs : nat -> tm -> tm.

Definition value (t : tm) : Prop := match t with
  | abs _ _ => True
  | _ => False
  end.

Notation " :λ x , N " := (abs x N) (at level 20).
Notation " M @ N " := (app M N) (at level 60). 
Coercion var : nat >-> tm.

Fixpoint fvs (e:tm) : list nat := match e with
  | var v =>  v::nil
  | abs v b => remove v (fvs b)
  | app m n => fvs m ++ fvs n
  end.

Definition closed (t:tm) := fvs t = nil.

Fixpoint vars (e:tm) : list nat := match e with
  | var v => v::nil
  | abs v b => v::vars b
  | app m n => vars m ++ vars n
  end.

Reserved Notation "'[' x '//' y ']' t" (at level 20).
Fixpoint subst (x : nat) (x' : tm) (t : tm) : tm := match t with
  | var y => if eq_nat_dec x y then x' else t
  | m@n => [x'//x]m @ [x'//x]n
  | :λy,b => if eq_nat_dec x y then t else :λy,([x'//x]b) 
  end
where " '[' x '//' y ']' t " := (subst y x t).

Lemma subst_subset : forall t m x, subset (fvs ([t//x]m)) (fvs t ++ remove x (fvs m)).
intros. induction m. simpl. destruct (eq_nat_dec x n); crush. apply subset_app.
apply subset_id. simpl. rewrite app_subset_and. split. rewrite remove_app. rewrite app_assoc. apply
subset_app. assumption. apply subset_comm2. rewrite remove_app. rewrite <- app_assoc. apply
subset_comm2. apply subset_app. apply subset_comm2. assumption. simpl. destruct
(eq_nat_dec x n). simpl. subst. apply subset_comm2. apply subset_app. rewrite
remove_idem. apply
subset_id. simpl. rewrite <- subset_remove_cons. rewrite <- subset_eq in IHm.
rewrite <- subset_eq.  unfold subset'. intros. unfold subset' in IHm. apply IHm
in H. simpl.  rewrite in_app_iff in H. destruct H. right. rewrite in_app_iff.
left. assumption. destruct (eq_nat_dec n a). left. assumption. right. rewrite
in_app_iff. right. rewrite remove_dup. apply remove_not_in with (ns:=remove x (fvs m)). auto. assumption. Qed. 

Lemma fvs_lam_dom : forall v b d, subset (fvs (abs v b)) d <-> subset (fvs b) (v :: d). 
intros. split; intros. simpl in H. rewrite subset_remove_cons. assumption.
simpl. rewrite <- subset_remove_cons. assumption. Qed.

Lemma fvs_body_remove : ∀ x v b, In x (remove v (fvs b)) → In x (fvs (abs v b)). 
intros. simpl. assumption. Qed. 

Definition replace' : nat -> nat -> nat -> nat := fun y z x => if eq_nat_dec y x then z else x.
Definition replace (y z:nat) := map (replace' y z).

Lemma replace_not_in : forall x x' xs, x <> x' -> ~In x (replace x x' xs).
intros. unfold not. induction xs. auto. simpl. unfold replace'. destruct (eq_nat_dec x a). 
intros. destruct H0. symmetry in H0. auto. auto. intros. 
destruct H0. symmetry in H0. auto. auto. Qed. 

Lemma replace_remove : forall x x' xs, replace x x' (remove x xs) = remove x xs.
intros. induction xs. auto. simpl. destruct (eq_nat_dec x a). assumption. simpl.
unfold replace'. 
destruct (eq_nat_dec x a). apply n in e. inversion e. rewrite IHxs. reflexivity.
Qed. 

Lemma remove_replace_comp : forall x y z zs, ~In x zs -> z <> x -> z <> y ->  
(remove z (replace y x zs) = replace y x (remove z zs)). intros. induction zs.
auto. simpl in H.  apply not_or in H. destruct H. simpl. destruct (eq_nat_dec y
a). unfold replace'. subst. rewrite eq_nat_dec_refl. destruct (eq_nat_dec z x).
apply H0 in e. inversion e. destruct (eq_nat_dec z a). apply H1 in e. inversion
e. simpl. unfold replace'. apply IHzs in H2. rewrite eq_nat_dec_refl. rewrite
H2. reflexivity.  unfold replace'. simpl. destruct (eq_nat_dec z a). subst.
apply IHzs in H2. rewrite H2. destruct (eq_nat_dec y a). apply n in e. inversion
e. rewrite eq_nat_dec_refl. reflexivity. simpl.  unfold replace'. destruct
(eq_nat_dec y). destruct (eq_nat_dec z x). apply H0 in e0. inversion e0. apply
IHzs in H2. rewrite H2. reflexivity. simpl. destruct (eq_nat_dec z a). apply n0
in e. inversion e. apply IHzs in H2. rewrite H2. reflexivity.  Qed. 

Lemma replace_imp : forall x y xs, In x xs -> In y (replace x y xs). 
intros. unfold replace. assert (y = replace' x y x). unfold replace'. rewrite
eq_nat_dec_refl. reflexivity. rewrite H0 at 1.  apply in_map. assumption. 
Qed.
  
Lemma replace_id : forall x xs, replace x x xs = xs. 
intros. induction xs. auto. simpl. unfold replace'. destruct (eq_nat_dec x a). rewrite <- e. rewrite
IHxs. reflexivity. rewrite IHxs. reflexivity. Qed. 

Lemma replace_in : forall x y a xs, a <> y -> In a (replace x y xs) -> In a xs.
intros. destruct (eq_nat_dec a x). subst. apply replace_not_in with
(xs:=xs) in H. apply H in H0. inversion H0. induction xs. auto. simpl in H0.
simpl. destruct H0. unfold replace' in H0. destruct (eq_nat_dec x a0); simpl;
crush. crush. Qed.  

Lemma replace_cons : forall x x' xs ys, subset xs (x::ys) -> subset (replace x x' xs) (x'::ys). 
intros. destruct (eq_nat_dec x x'). subst. rewrite replace_id. assumption.
induction xs. simpl. auto. simpl in H. destruct H. destruct H. subst. apply IHxs
in H0. simpl. split. unfold replace'. rewrite eq_nat_dec_refl. left.
reflexivity. assumption. apply IHxs in H0. simpl. split. unfold replace'. destruct (eq_nat_dec x
a). left; reflexivity. right. assumption. assumption. Qed. 

Lemma ex1 : fvs (var 1) = cons 1 nil.
simpl. reflexivity. Qed.

Lemma ex2 : fvs (abs 1 (var 1)) = nil.
simpl. reflexivity. Qed.

Lemma ex3 : fvs (app (var 1) (var 1)) = cons 1 (cons 1 nil).
simpl. reflexivity. Qed.
