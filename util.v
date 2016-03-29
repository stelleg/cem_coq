(* General utility file, should break up into smaller modules, e.g. maps, Sets,
etc. *)

Require Import List Basics EqNat Logic.Decidable.
Require Import Arith.Peano_dec.
Require Import CpdtTactics.
Require Import Logic.ProofIrrelevance.
Require Import Unicode.Utf8.
Require Import Compare_dec.

Definition Map a b := list (a * b).

Lemma wrap : forall A B (f:A -> B), f = fun a:A => f a. auto. Qed.  

Fixpoint subset {A} (l : list A) (m: list A) : Prop := match l with
  | nil => True
  | cons x xs => In x m /\ subset xs m
  end.

Notation " a ⊆ b " := (subset a b) (at level 30).
Definition rel (A : Type) := A → A → Prop.
Definition relation (A B : Type) := A → B → Prop.
Definition equiv {A B} := ∀ (a a':A) (b b':B) (ra : rel A) (rb : rel B)
  (e : relation A B), e a b → ra a a' → rb b b' → e a' b'.

Lemma or_imp : forall a b c : Prop, (a \/ b -> c) <-> (a -> c) /\ (b -> c).
intros. split; intros. split; intros.  apply or_introl with (B:=b) in H0. apply H in H0.
assumption. apply or_intror with (A:=a) in H0. apply H in H0. assumption.
destruct H. destruct H0. apply H in H0. assumption.  apply H1 in H0. assumption.
Qed.

Lemma cons_neq {A} : ∀ (x:A) xs, xs <> x::xs.
intros. induction xs. unfold not. intros. inversion H. unfold not. intros.
inversion H. apply IHxs in H2. auto. Qed. 

Lemma app_eq_l {A} : ∀ a b c : list A, a ++ b = a ++ c → b = c. 
intros. induction a. rewrite app_nil_l in H. rewrite app_nil_l in H. assumption.
inversion H. apply IHa; assumption. Qed. 

Lemma app_eq_r {A} : ∀ b a c : list A, a ++ b = c ++ b → a = c. 
intros b. induction b; intros. rewrite app_nil_r in H. rewrite app_nil_r in H.
assumption. assert (b = nil ++ b). reflexivity. rewrite H0 in H. rewrite
app_comm_cons in H. rewrite app_assoc in H. rewrite app_assoc in H. apply IHb in
H. apply app_inj_tail in H. destruct H. assumption. Qed. 

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

Fixpoint forevery {a} (l:list a) (p : a → Prop) : Prop := match l with
  | cons x xs => p x ∧ forevery xs p
  | nil => True
  end.

Lemma forevery_map {A B} : ∀ (f:A→B) xs p, forevery (map f xs) p = forevery xs (compose p f).
intros. induction xs. simpl. auto. simpl. f_equal. assumption. Qed.

Definition domain {a b} (m : Map a b) : list a := map (@fst a b) m.
Definition codomain {a b} (m : Map a b) : list b := map (@snd a b) m.

Definition isfresh {a} (h : Map nat a) (n : nat) : Prop := ¬ In n (domain h). 
Axiom fresh : ∀ {a:Type} (h:Map nat a), {n | isfresh h n}.
Definition fresh' {A} (x: nat) (Φ : Map nat A) :=
  ∃ p, fresh Φ = exist (isfresh Φ) x p. 

Inductive unique {a} : list a → Prop := 
  | unil : unique nil
  | ucons : ∀ x xs, ¬ In x xs → unique xs → unique (cons x xs). 

Definition fmap {A B C} (f : B -> C) : A * B -> A * C  := fun x => match x with
  | (a, b) => (a, f b) end. 

Definition forevery_codomain {a b} (m:Map a b) (p : b → Prop) : Prop := forevery
  m (λ x, match x with (k,v) => p v end).


Lemma domain_fmap : forall A B C (f:B->C) (xs:Map A B),  domain (map
(fmap f) xs) = domain xs.
intros. induction xs. crush. crush. Qed. 

Lemma domain_inf {a b} : ∀ xs (y:a) (m m':b) ys, domain (xs ++ (y,m) :: ys) = 
                                   domain (xs ++ (y,m') :: ys).
intros. unfold domain. rewrite map_app. simpl. rewrite map_app. simpl.
reflexivity. Qed.                                    

Lemma inf_indomain {a b} : ∀ (k:a) (v:b) ys zs, In k (domain (ys ++ (k,v) :: zs)). 
intros. subst. unfold domain. rewrite map_app. apply
in_or_app. apply or_intror. simpl. auto. Qed. 

Lemma forevery_app : forall a (xs ys:list a) p, forevery (xs ++ ys) p <->
  forevery xs p ∧ forevery ys p.
  intros. induction xs. simpl. split. auto. intros. destruct H. auto. simpl. 
  split. intros. destruct H. apply IHxs in H0. destruct H0. split. auto. auto. 
  intros. rewrite and_assoc in H. destruct H. rewrite <- IHxs in H0. auto. Qed.  

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

Lemma eq_dec_refl : forall A (m:A) (eq : ∀ a b:A, {a = b} + {a <> b}) , eq m m = left eq_refl.
intros. destruct (eq m m). assert (∀ p q : m = m, p = q). apply
proof_irrelevance. specialize H with e eq_refl. rewrite H. reflexivity. crush.
Qed.  

Lemma eq_nat_dec_neq : forall m n (p : m <> n), eq_nat_dec m n = right p.
intros. destruct (eq_nat_dec m n). unfold not in p. subst. assert (n = n).
reflexivity.  apply p in H. inversion H. assert (p = n0). rewrite
proof_irrelevance with (P := m <> n) (p1 := p) (p2 := n0). reflexivity. subst.
reflexivity. Qed.

Lemma eq_dec_neq : forall A (m n:A) (eq : ∀ a b:A, {a = b} + {a <> b}) (p : m <> n), eq m n = right p.
intros. destruct (eq m n). unfold not in p. subst. assert (n = n).
reflexivity.  apply p in H. inversion H. assert (p = n0). rewrite
proof_irrelevance with (P := m <> n) (p1 := p) (p2 := n0). reflexivity. subst.
reflexivity. Qed.

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

Definition lookup {a} (x:nat) (l:list (nat * a)) : option a := 
  match find (λ p, beq_nat x (fst p)) l with 
    | None => None
    | Some (k,v) => Some v
  end.

Definition lookup_total {B} : ∀ (m : Map nat B) a, In a (domain m) → ∃ b,
  lookup a m = b. 
intros. induction m. crush. simpl in H. destruct a0. destruct (eq_nat_dec a n). destruct H. simpl in H.
simpl. symmetry in e. subst. exists (Some b). unfold lookup. simpl. rewrite <- beq_nat_refl.  reflexivity.
apply IHm in H. simpl. subst. exists (Some b). unfold lookup. simpl. rewrite <-
beq_nat_refl. reflexivity. destruct H. simpl in H. symmetry in H. apply n0 in H.
inversion H. unfold lookup. simpl. rewrite <- beq_nat_false_iff in n0. rewrite
n0. apply IHm in H. assumption. Qed. 

Definition lookup_codomain {B} : ∀ (m : Map nat B) a b, lookup a m = Some b → In b
(codomain m). 
intros. induction m. inversion H. simpl. unfold lookup in H. simpl in H.
destruct a0. simpl in H. destruct (beq_nat a n). simpl. inversion H. subst.
auto. apply IHm in H. auto. Qed. 

Definition flip {A B C} (f : A → B → C) : B → A → C := fun b a => f a b.

Lemma in_domain_lookup {b} : ∀ (m : Map nat b) k, In k (domain m) →
  ∃ v, lookup k m = Some v.
  intros. induction m. crush. destruct a. simpl in H. destruct (eq_nat_dec k n).
  subst. simpl. unfold lookup. simpl. rewrite <- beq_nat_refl. apply ex_intro with b0. reflexivity.
  simpl. destruct H. symmetry in H. apply n0 in H. inversion H. apply IHm in H.
  destruct H. unfold lookup. simpl. rewrite <- beq_nat_false_iff in n0. rewrite
  n0. exists x. unfold lookup in H. rewrite H. reflexivity. Qed.

Lemma lookup_in_domain {b} : ∀ (m : Map nat b) k, (∃ v, lookup k m = Some v) → 
  In k (domain m). 
intros. destruct H. induction m. inversion H. destruct (eq_nat_dec k (fst a)).
destruct a. simpl in e. subst. simpl. auto. unfold lookup in H. simpl in H. rewrite <-
beq_nat_false_iff in n. rewrite n in H. apply IHm in H. simpl. apply or_intror.
assumption. Qed.

Lemma lookup_in_domain_iff {b} : ∀ (m : Map nat b) k, 
(∃ v, lookup k m = Some v) 
        ↔
  In k (domain m). 
split. apply lookup_in_domain. apply in_domain_lookup. Qed. 

Lemma subset_domain_map {b} : ∀ l (m : Map nat b), subset l (domain m) → forevery l (λ k,
  ∃ v, lookup k m = Some v).
intros. induction l. crush. simpl in H. destruct H. apply IHl in H0. simpl.
split. Focus 2. assumption. apply in_domain_lookup. assumption. Qed. 

Lemma forevery_codomain_lookup {b} : ∀ (m : Map nat b) p l v, forevery_codomain m p →
  lookup l m = Some v → p v.
intros. induction m. inversion H0. destruct a. destruct (eq_nat_dec l n). subst.
unfold lookup in H0.  simpl in H0.  rewrite <- beq_nat_refl in H0. inversion H0.
subst. unfold forevery_codomain in H.  simpl in H. crush. unfold lookup in H0.
simpl in H0. rewrite <- beq_nat_false_iff in n0. rewrite n0 in H0. unfold
forevery_codomain in H.  simpl in H.  destruct H. apply IHm in H1. assumption.
assumption. Qed. 

Lemma forevery_inf {a} : ∀ (xs ys:list a) (y:a) p, forevery (xs ++ y :: ys) p →
  p y.
intros. apply forevery_app in H. crush. Qed. 

Lemma forevery_impl {a} : ∀ xs (p p':a→Prop), (∀ a, p a → p' a) → forevery xs p →
  forevery xs p'. 
intros. induction xs. crush. crush. Qed. 
  
Definition max (m n : nat) : nat := match le_gt_dec m n with 
  | left _ => m
  | right _ => n
  end.

Definition maximum : list nat → nat := fold_right max 0.

Definition replace {K V} (eq : K → K → bool) (k : K) (v : V) :
  Map K V → Map K V := map (λ e, match e with | (k', v') => if eq k k' then
    (k', v) else e end). 

Lemma unique_inf {a b} : ∀ xs ys xs' ys' (k:a) (v v':b), unique (domain (xs ++ (k,v) :: ys)) → 
  xs ++ (k,v) :: ys = xs' ++ (k,v') :: ys' → xs = xs' ∧ v = v' ∧ ys = ys'.
intros.  generalize dependent xs'. generalize dependent ys'. induction xs.
intros; induction xs'. inversion H0. subst. auto. inversion H0.  subst. simpl in H.
inversion H; subst. assert (In k (domain (xs' ++ (k,v') :: ys'))). apply
inf_indomain. apply H3 in H1. inversion H1. simpl in H. destruct a0. inversion H. subst.
specialize (IHxs H3). intros. inversion H0. destruct xs'. inversion H0. subst.
inversion H; subst. assert (In k (domain (xs ++ (k,v) :: ys))). apply
inf_indomain. apply H6 in H1. inversion H1. inversion H4; subst. specialize
(IHxs ys' xs' H6). split. f_equal. destruct IHxs; auto. destruct IHxs. destruct
H5. split; auto. Qed.
  
Lemma unique_domain_lookup {b} : ∀ xs k (v:b), unique (domain xs) → 
  (∃ ys zs, xs = ys++(k,v)::zs) → lookup k xs = Some v.
intros. induction xs. simpl. destruct H0. destruct H0. apply app_cons_not_nil in H0. inversion H0. 
destruct H0. destruct H0. destruct x. inversion H0.  subst. unfold lookup.
simpl.  rewrite <- beq_nat_refl. reflexivity. unfold lookup. simpl. destruct a.
inversion H. subst. inversion H0. subst. unfold domain in H3. rewrite map_app in
H3. rewrite in_app_iff in H3. apply or_imp in H3. destruct H3. simpl in H2.
apply or_imp in H2. destruct H2. assert (k <> n). assumption.  rewrite <-
beq_nat_false_iff in H5. simpl.  rewrite H5. apply IHxs. assumption. exists x,
x0. reflexivity. Qed.

Lemma replace_not_in {a} : ∀ xs l (c:a), ¬In l (domain xs) → replace beq_nat l c xs = xs.
intros. induction xs. auto. destruct a0. destruct (eq_nat_dec l n). subst. simpl
in H. apply or_imp in H. destruct H. specialize (H eq_refl). inversion H. simpl.
rewrite <- beq_nat_false_iff in n0. rewrite n0. simpl in H. unfold not in H. rewrite or_imp in H. 
destruct H. apply IHxs in H0. rewrite H0. reflexivity. Qed.

Lemma replace_inf {a} : ∀ xs l (c c':a) ys, 
  unique (domain (xs ++ (l,c) :: ys)) →
  replace beq_nat l c' (xs ++ (l,c) :: ys) = xs ++ (l,c') :: ys.
intros. induction xs. simpl. rewrite <- beq_nat_refl. simpl in H. inversion H.
subst. rename c into C. apply replace_not_in with (c:=c') in H2. rewrite H2.
reflexivity. simpl. destruct a0. destruct (eq_nat_dec l n). subst. inversion H.
subst. specialize (H2 (inf_indomain n c xs ys)). inversion H2.  rewrite <-
beq_nat_false_iff in n0. rewrite n0. inversion H; subst. apply IHxs in H3.
rewrite H3. reflexivity. Qed. 

