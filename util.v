Require Import List Basics EqNat Logic.Decidable.
Require Import Arith.Peano_dec.
Require Import CpdtTactics.

Lemma wrap : forall A B (f:A -> B), f = fun a:A => f a. auto. Qed.  

Fixpoint subset {A} (l : list A) (m: list A) : Prop := match l with
  | nil => True
  | cons x xs => In x m /\ subset xs m
  end.

Lemma or_imp : forall a b c : Prop, (a \/ b -> c) <-> (a -> c) /\ (b -> c).
intros. split; intros. split; intros.  apply or_introl with (B:=b) in H0. apply H in H0.
assumption. apply or_intror with (A:=a) in H0. apply H in H0. assumption.
destruct H. destruct H0. apply H in H0. assumption.  apply H1 in H0. assumption.
Qed.

Definition subset' {A} (l m : list A) : Prop := forall a, In a l -> In a m.

Definition forall_and {A} : forall (x y:A -> Prop), (forall a:A, x a /\ y a) <-> (forall
a:A, x a) /\ (forall a:A, y a).
intros. split;  intros. split; intros; specialize H with a; destruct H; assumption. 
destruct H.  specialize H with a. specialize H0 with a. split; assumption. Qed.

Definition forall_or {A} : forall (x y z:A -> Prop), (forall a:A, x a \/ y a -> z a) <-> (forall
a:A, x a -> z a) /\ (forall a:A, y a -> z a).
intros. split;  intros. split; intros. apply or_introl with (B:=y a) in H0.
apply H in H0. assumption. apply or_intror with (A:=x a) in H0. apply H in H0.
assumption. destruct H. destruct H0. apply H in H0. assumption. apply H1 in H0.
assumption. Qed.

Lemma subset'_cons {A} : forall (x : A) (l m : list A), 
  subset' (x::l) m -> subset' l m.
intros.  unfold subset' in H. unfold In at 1 in H. setoid_rewrite or_imp in H.
apply forall_and in H. destruct H. assumption. Qed. 

Lemma subset_eq : forall A (l m : list A), subset' l m <-> subset l m.
intros. induction l. split. intros. unfold subset. auto. intros. unfold subset'.
intros. inversion H0. split; intros. assert (In a (a::l)). unfold In. left.
reflexivity. apply H in H0. unfold subset. split. assumption. 
assert (subset' l m). apply subset'_cons in H. assumption. rewrite IHl in H1.
assumption. unfold subset'. unfold subset in H. destruct H. rewrite <- IHl in
H0. unfold In at 1. setoid_rewrite or_imp. rewrite forall_and. split. intros.
rewrite <- H1. assumption. assumption. Qed.

Lemma subset_nil : forall A ms, subset (@nil A) ms.
intros. unfold subset. auto. Qed. 

Lemma subset_nil2 : forall A ms, subset ms (@nil A) -> ms = nil.
intros. rewrite <- subset_eq in H. unfold subset' in H. induction ms.
reflexivity. simpl in H. specialize H with a. destruct H. left. reflexivity.
Qed. 

Fixpoint remove (x : nat) (l : list nat) := match l with
  | nil => nil
  | cons y ys => if eq_nat_dec x y then remove x ys else y::remove x ys
  end.

Lemma remove_in : forall (n : nat) ns, ~ In n (remove n ns).
intros. induction ns. auto. unfold remove. destruct (eq_nat_dec n a).
assumption. fold remove. unfold In. unfold not. rewrite not_or_iff. split.
intros. symmetry in H. apply n0 in H. assumption. assumption. Qed.

Lemma remove_app : forall (n : nat) ns ms, remove n (ns ++ ms) = remove n ns ++
remove n ms.
intros. induction ns. auto. simpl. rewrite IHns. destruct (eq_nat_dec n a).
auto.  apply app_comm_cons. Qed. 

Lemma remove_idem : forall (n : nat) ns, remove n (remove n ns) = remove n ns.
intros. induction ns. simpl. auto. simpl. destruct (eq_nat_dec n a). assumption. 
simpl. destruct (eq_nat_dec n a). apply n0 in e.  inversion e. rewrite IHns.
reflexivity. Qed. 

Lemma eq_nat_dec_refl : forall m, eq_nat_dec m m = left eq_refl.
intros. induction m. auto. simpl. rewrite IHm. simpl. reflexivity. Qed. 

Lemma remove_dup : forall (n m : nat) ns, remove n (remove m ns) = remove m
(remove n ns).
intros. induction ns. auto. simpl. destruct (eq_nat_dec m a). destruct
(eq_nat_dec n a). rewrite e. rewrite e0. reflexivity. rewrite IHns. rewrite e.
simpl. rewrite eq_nat_dec_refl. reflexivity. destruct (eq_nat_dec n a). rewrite
e. simpl. rewrite eq_nat_dec_refl. rewrite <- e. rewrite IHns. reflexivity.
simpl. destruct (eq_nat_dec n a). apply n1 in e. inversion e. destruct
(eq_nat_dec m a). apply n0 in e. inversion e. rewrite IHns. reflexivity. Qed. 

Lemma or_false : forall p : Prop, p \/ False <-> p. intros. split; intros.
destruct H. assumption. inversion H. apply or_introl.  assumption. Qed.

Lemma remove_not_in : forall (n v : nat) ns, n <> v -> (In n (remove v ns) <-> In n ns).
intros. induction ns.  split; intros; inversion H0. split; intros; simpl. simpl
in H0. destruct (eq_nat_dec v a). apply IHns in H0. right. assumption. simpl in
H0. destruct H0. left; assumption. apply IHns in H0. right. assumption. destruct
(eq_nat_dec v a). rewrite IHns. simpl in H0. destruct H0. rewrite H0 in e.
symmetry in e. apply H in e. inversion e. assumption. simpl. simpl in H0.
destruct H0. left. assumption. right. rewrite <- IHns in H0. assumption. Qed.

Lemma subset_tail : forall (xs ys:list nat), subset xs (tl ys) -> subset xs ys.
intros. induction xs. auto. simpl in H. simpl. destruct H. split. destruct ys.
auto. simpl in H. apply in_cons. assumption. apply IHxs in H0. assumption. Qed. 

Lemma noteq_comm {A} : forall (m n : A), m <> n -> n <> m.
intros. auto. Qed. 

Lemma beq_nat_comm : forall m n, beq_nat n m = beq_nat m n. 
intros. destruct (eq_nat_dec m n).  rewrite e. reflexivity. assert (n <> m).
apply noteq_comm in n0. assumption. apply
beq_nat_false_iff in n0. apply beq_nat_false_iff in H. rewrite n0. rewrite H.
reflexivity. Qed.

Lemma let_inline : forall A (b c:A) f, f (let a := b in c) -> let a := b in (f c).
auto. Qed.

Lemma subset_singleton : forall (x y : nat) xs, subset (x::xs) (y::nil) -> x = y.
intros. inversion H. destruct H0. symmetry. assumption. inversion H0. Qed.

Lemma subset_cons {A} : forall (x : A) a l, subset a l -> subset a (x::l). intros.
induction a. auto. inversion H. split. apply in_cons. assumption. 
apply IHa in H1. assumption. Qed.  

Lemma cons_subset {A} : forall (x: A) xs ys, subset xs ys -> subset (x::xs) (x::ys).
intros. unfold subset. simpl. split. left. reflexivity. apply subset_cons.
assumption. Qed. 

Lemma subset_remove : forall n ns, subset (remove n ns) ns.
intros. induction ns. apply subset_nil. unfold remove. destruct (eq_nat_dec n
a). fold remove. apply subset_cons. assumption. fold remove. apply cons_subset.
assumption. Qed.

Lemma subset_in_cons : forall (n:nat) ns ms, ~In n ns -> subset ns (n::ms) -> subset ns ms. 
intros.  rewrite <- subset_eq. rewrite <- subset_eq in H0. unfold subset' in
H0. unfold In in H0 at 2. unfold subset'. intros. specialize H0 with a. 
destruct (eq_nat_dec n a). rewrite <- e in H1. unfold not in H. apply H in H1.
inversion H1. apply H0 in H1. destruct H1. apply n0 in H1. inversion H1.
assumption. Qed. 

Lemma symmetry : forall p q : Prop, p = q <-> q = p. intros. split; intros;
symmetry in H; assumption. Qed. 

Lemma subset_remove_cons : forall a v vs, subset a (v::vs) <-> subset (remove v a) vs. 
intros. split; intros. rewrite <- subset_eq. rewrite <- subset_eq in H. unfold subset' in H.  
unfold subset'. simpl in H. intros. specialize H with a0. destruct (eq_nat_dec
a0 v). rewrite e in H. rewrite e in H0. apply remove_in in H0. inversion H0.
assert (a0 <> v). assumption.  apply remove_not_in with (ns:=a) in n. rewrite n
in H0. apply H in H0. destruct H0. symmetry in H0. apply H1 in H0. inversion H0.
assumption.  rewrite <- subset_eq in H. unfold subset' in H. induction a. apply
subset_nil.  simpl. split. simpl in H. destruct (eq_nat_dec v a). left.
assumption. simpl in H. specialize H with a. assert (a = a).  reflexivity. apply
or_introl with (B:=In a (remove v a0)) in H0. apply H in H0. right. assumption.
simpl in H.  destruct (eq_nat_dec v a). apply IHa in H. assumption. simpl in H.
rewrite forall_or in H. destruct H. apply IHa in H0. assumption. 
Qed.


Lemma truand : forall a:Prop, True /\ a -> a.
intros. destruct H. auto. Qed. 

Lemma app_subset_and {A} : forall xs ys zs: list A, subset (xs ++ ys) zs <-> (subset xs zs /\ subset ys zs).
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

Lemma subset_id {A} : forall xs:list A, subset xs xs. 
intros. induction xs. unfold subset. auto. unfold subset. split. unfold In.
auto. apply subset_cons. auto. Qed. 

Lemma subset_app_id {A} : forall xs ys zs:list A, subset ys zs -> subset (xs ++ ys) (xs ++ zs) .
intros. induction xs. simpl. assumption. unfold subset. simpl. split. left.
reflexivity. apply subset_cons. assumption. Qed.   

Lemma subset_app {A} : forall xs ys zs:list A, subset xs ys -> subset xs (ys ++ zs).
intros. rewrite <- subset_eq. rewrite <- subset_eq in H. unfold subset'. intros. rewrite
in_app_iff.  left. apply H in H0.  assumption. Qed. 

Lemma cons_app {A}: forall (x:A) xs, x :: xs = x::nil ++ xs.
intros. rewrite app_nil_l. reflexivity. Qed.

Lemma subset_comm1 {A} : forall xs ys zs:list A, subset (xs ++ ys) zs -> subset (ys ++ xs) zs.
intros. apply app_subset_and. apply and_comm. apply app_subset_and. assumption.
Qed. 

Lemma subset_comm2 {A} : forall xs ys zs:list A, subset xs (ys ++ zs) -> subset xs (zs ++ ys). 
intros. induction xs. auto. simpl. split. simpl in H. destruct H. apply
in_app_or in H. apply or_comm in H. apply in_or_app in H. assumption. simpl in
H. destruct H. apply IHxs in H0. assumption. Qed. 

Lemma subset_trans {A}: forall xs ys zs:list A, subset xs ys -> subset ys zs -> subset xs zs. 
intros. induction xs. unfold subset. auto. split. destruct H. rewrite <- subset_eq
in H0. unfold subset' in H0. apply H0 in H. assumption. simpl in H. destruct H.
apply IHxs in H1. assumption. Qed. 

Definition set_equiv {A} (xs ys : list A) : Prop := subset xs ys /\ subset ys xs. 

Lemma subset_swap {A} : forall (n v : A) vs, set_equiv (n::v::vs) (v::n::vs).
intros. unfold set_equiv. simpl. split; split. right. left. reflexivity. split.
left. reflexivity. repeat (apply subset_cons). apply subset_id. right. left.
reflexivity. split. left. reflexivity. repeat (apply subset_cons). apply
subset_id. Qed.


