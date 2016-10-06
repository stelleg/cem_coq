Require Import db util.
Require Import Arith.EqNat.
Require Import List Unicode.Utf8 Arith.Peano_dec Basics.
Require Import CpdtTactics JRWTactics.
Require Import Datatypes.

Import ListNotations. 

Record closure : Type := close {
  clos_tm : tm;
  clos_env : nat
}.

Inductive cell : Type := cl : closure → nat → cell.
Definition clclose : cell → closure := λ c, match c with cl c' e => c' end.

Definition heap := Map nat cell.

Record configuration : Type := conf {
  reachable : heap;
  unreachable : heap;
  st_clos : closure
}.

Definition st_heap : configuration → heap := λ c, unreachable c ++ reachable c. 

Definition I (e : tm) : configuration := conf nil nil (close e 0).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Ψ & Φ ⟩ m " := (conf Ψ Φ m) (at level 40).
Notation " ⟨ Υ & b , Φ , Ψ ⟩ N " := (conf Υ (Ψ ++ Φ ++ b :: nil) N) (at level 40).
Notation " ⟨ Υ , b & Ψ ⟩ N " := (conf (b :: Υ) Ψ N) (at level 40).
Notation " ⟨ Υ , b , Φ & Ψ ⟩ N " := (conf (Φ ++ b :: Υ) Ψ N) (at level 40).

(* cactus lookup: lookup deBruijn index i at location x in heap h yields
location y *)
Inductive cactus_lookup : nat → nat → heap → nat * cell → Prop :=
  | zero : forall x Φ Υ c,  cactus_lookup 0 x (Φ ++ (x ↦ c) :: Υ) (x,c)
  | next : forall x y Φ c Υ i p, cactus_lookup i x (Φ ++ (y ↦ cl c x) :: Υ) p → 
            cactus_lookup (S i) y (Φ ++ (y ↦ cl c x):: Υ) p.

Fixpoint clu (v env:nat) (h:heap) : option (nat * closure) := match lookup env h with
  | None => None
  | Some (cl c a) => match v with
    | S n => clu n a h
    | 0 => Some (env, c)
    end
  end.

Definition closed_under (c : closure) (h : heap)  : Prop := match c with
  | close t e => forevery (fvs t) 
      (λ x, ∃e' c', clu x e h = Some (e',c'))
  end.

Definition closed (t : tm) : Prop := closed_under (close t 0) nil.

Fixpoint well_formed_heap (h : heap) : Prop := match h with
  | nil => True
  | v↦cl t e::h => isfresh (domain h) v ∧  closed_under t h ∧ well_formed_heap h
  end. 

Definition well_formed (c : configuration) : Prop := match c with 
  | conf r ur t => closed_under t r ∧ well_formed_heap (ur ++ r)
  end.

Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M B x y z Φ Φ' Υ Ψ v e, clu v z (Υ ++ x↦cl M y::Φ) = Some (x, M) → 
      ⟨Φ & x↦cl M y, Υ, Ψ⟩M ⇓ ⟨Φ' & x↦cl M y, Υ, Ψ⟩close (:λB) e →
    ⟨Φ, x↦cl M y, Υ & Ψ⟩close v z ⇓ ⟨Φ', x↦ cl (close (:λB) e) y, Υ & Ψ⟩close (:λB) e
  | Abs : ∀ N Φ Ψ e, ⟨Φ & Ψ⟩close (:λN) e ⇓ ⟨Φ & Ψ⟩close (:λN) e
  | App : ∀ N M B B' Φ Φ' Ψ Υ f e ne ae, 
                  fresh' f (domain (Ψ ++ Φ')) → 
          ⟨Φ & Ψ⟩close M e ⇓ ⟨Φ' & Ψ⟩close (:λB) ne → 
      ⟨Φ', f ↦cl (close N e) ne & Ψ⟩close B f ⇓ ⟨Υ & Ψ⟩close (:λB') ae   →
              ⟨Φ & Ψ⟩close (M@N) e ⇓ ⟨Υ & Ψ⟩close (:λB') ae
where " c1 '⇓' c2 " := (step c1 c2).

Definition configuration' := sig well_formed.
Definition step' (c1 c2: configuration') : Prop := match (c1, c2) with
  | (exist c1 _, exist c2 _) => step c1 c2 end.

Lemma well_formed_heap_app : ∀ Φ Ψ, well_formed_heap (Φ ++ Ψ) → well_formed_heap Ψ. 
intros. induction Φ. assumption. apply IHΦ. destruct a. destruct c. destruct H.
destruct H0. auto. Qed. 

Lemma well_formed_inf : ∀ c x c' n Ψ Φ Υ, 
  well_formed (⟨Φ, x ↦ cl c' n, Υ & Ψ⟩c) → 
  well_formed (⟨Φ & x ↦ cl c' n, Υ, Ψ⟩c').
intros. split. simpl in H. destruct H. clear H. apply well_formed_heap_app in
H0. apply well_formed_heap_app in H0. simpl in H0. destruct H0. destruct H0.
assumption. inversion H. repeat (rewrite <- app_assoc). simpl. assumption. Qed.

Lemma forevery_cons {A} : ∀ (p:A→Prop) (x:A) xs, p x → forevery xs p → forevery (x::xs) p. 
intros. simpl. split; assumption. Qed. 

Lemma clu_inf : ∀ x x' c c' e e'  Ψ Φ clo n, 
  clu x e (Φ ++ x' ↦ cl c e' :: Ψ) = Some (n, clo) →
  ∃ clo', clu x e (Φ ++ x' ↦ cl c' e' :: Ψ) = Some (n, clo').
intros x. induction x. intros. simpl in H. remember (lookup e (Φ ++ x' ↦ cl c e' :: Ψ)).
simpl. destruct o. symmetry in Heqo. apply (ex_intro (λ x, lookup e (Φ ++ x' ↦ cl
c e' :: Ψ) = Some x) c0) in Heqo. destruct Heqo. apply lookup_domain in H0. rewrite
domain_inf with (m':= cl c' e') in H0. apply in_domain_lookup in H0.
destruct H0. rewrite e0. destruct x. destruct c0. inversion H. subst. clear H.
destruct x0.  exists c0. reflexivity. inversion H. intros. specialize (IHx x' c
c').  simpl in H. remember (lookup e (Φ ++ x' ↦  cl c e' :: Ψ)). destruct o.
destruct c0. specialize (IHx n0 e' Ψ Φ clo n H). destruct IHx. simpl. remember
(lookup e (Φ ++ x' ↦ cl c' e' :: Ψ)). destruct o. destruct c1. assert (n1 = n0).
clear H0. clear H. induction Φ.  simpl in Heqo. simpl in Heqo0. unfold lookup in
Heqo. unfold lookup in Heqo0.  simpl in Heqo. simpl in Heqo0. destruct (beq_nat
e x').  inversion Heqo. subst.  inversion Heqo0. subst. reflexivity. rewrite <-
Heqo in Heqo0.  inversion Heqo0.  subst. reflexivity. destruct a. unfold lookup
in Heqo.  unfold lookup in Heqo0. simpl in Heqo. simpl in Heqo0. destruct
(beq_nat e n2).  rewrite <- Heqo in Heqo0. inversion Heqo0. subst. reflexivity.
simpl in Heqo.  simpl in Heqo0. apply IHΦ. assumption. assumption. subst. exists
x0. assumption. symmetry in Heqo. apply (ex_intro (λ x, lookup e (Φ ++ x' ↦ cl c
e' :: Ψ) = Some x) (cl c0 n0)) in Heqo. destruct Heqo. apply lookup_domain in H1. rewrite
domain_inf with (m':=cl c' e') in H1. apply in_domain_lookup in H1. destruct
H1. rewrite e0 in Heqo0. inversion Heqo0. inversion H. Qed. 

Lemma cactus_lookup_trans : ∀ x e h n c e' y p, 
  cactus_lookup x e h (n, cl c e') →
  cactus_lookup y e' h p →
  cactus_lookup (S x + y) e h p.
intros. remember (n, cl c e'). induce H. inversion Heqp0. subst.
clear Heqp0. simpl. apply next in H0.  assumption. simpl in *. specialize
(IHcactus_lookup _ _ _ _ _ eq_refl H0). apply next in
IHcactus_lookup. assumption. Qed. 

Lemma next' : ∀ x e h p, 
  cactus_lookup (S x) e h p ↔ ∃ c e', cactus_lookup 0 e h (e, cl c e')   
                                    ∧ cactus_lookup x e' h p. 
split; intros. 
- inversion H. subst. induce H1. inversion H. subst. inversion H4.
  subst. exists c1, x. split. rewrite H0. constructor. constructor. inversion H.
  subst. rewrite H3 in H5. exists c1, x0. split. constructor. rewrite H3.
  assumption. 
- destruct H. destruct H. destruct H. induce H0. inversion H. subst. apply
  next. rewrite H0. constructor. inversion H. subst. apply next. rewrite H1.
  apply IHcactus_lookup with (x0:=c). constructor. Qed.

Lemma cactus_lookup_minus : ∀ x e h y p, 
  cactus_lookup (S x) e h p → y <= x →
  ∃ n c e', cactus_lookup (x - y) e h (n, cl c e') ∧
            cactus_lookup y e' h p. 
intros. apply next' in H. destruct H. destruct H. destruct H. induce H1.
inversion H0. subst. inversion H. subst. simpl. exists e, x0, x. split.
constructor. rewrite H1. constructor. inversion H. subst. specialize
(IHcactus_lookup y (pred y0) c (zero _ _ _ _)). apply Le.le_pred in H0. simpl in
H0. destruct H0. destruct IHcactus_lookup with. simpl. inversion H. nduction y.
subst. apply next' in H.  destruct H. destruct H. destruct H. inversion H.
subst. induction x. destruct (x
- y) eqn:xy. rewrite NPeano.Nat.sub_0_le in xy. assert (x=y). apply
  Le.le_antisym; auto. subst. induction H. subst. destruct p. clear H0 xy.
induction H. apply cactus_lookup_trans in H with (x:=0) (e:=e) (n:=n) (c:=c).
subst. destruct p. destruct c. inversion H.  subst. exists n, c, x. split;
auto. induce H2. inversion H4. subst. apply zero. inversion H. subst.
remember (S x). induce H. inversion Heqn. inversion Heqn. subst.
 



Lemma clu_cactus_lookup : ∀ x e h n c, clu x e h = Some (n, c) → ∃ e', 
  cactus_lookup x e h (n, cl c e').
induction x; intros. inversion H. destruct (lookup e h) eqn:lue. destruct c0.
exists n0. inversion H1. subst. apply lookup_e_inf in lue. destruct lue.
destruct H0. subst. inversion H1. subst.  constructor. inversion H1. inversion
H. destruct (lookup e h) eqn:lueh. destruct c0. apply IHx in H1. apply
lookup_e_inf in lueh. destruct lueh. destruct H0.  subst. destruct H1. exists
x2. apply next in H0. assumption. inversion H1. Qed.

Lemma cactus_lookup_clu : ∀ x e h n c e', unique (domain h) → 
  cactus_lookup x e h (n, cl c e') → clu x e h = Some (n, c). 
intros. simpl in *. remember (n, cl c e'). induce H0. inversion
Heqp. subst. simpl. rewrite lookup_inf; auto. simpl. destruct c eqn:ce.  rewrite
lookup_inf. apply IHcactus_lookup. destruct c0. simpl. rewrite lookup_inf.
destruct c eqn:ce. apply IHcactus_lookup. assumption.  assumption. Qed. 

Lemma clu_next : ∀ x e h l c,
  clu (S x) e h = Some (l, c) →
  ∃ l' c', clu x e h = Some (l', c') 
       ∧ lookup l' h = Some (cl c' l).
intros. induction x. inversion H. destruct (lookup e h) eqn:eh. destruct c0.
destruct (lookup n h) eqn:nh. destruct c1. inversion H1. subst. exists e, c0.
simpl. rewrite eh. auto. inversion H1. inversion H1. inversion H. destruct
(lookup e h) eqn:lu. destruct c0. destruct (lookup n h) eqn:lun. destruct c1.
ubst. 

Lemma clu_minus : ∀ x y e h p, 
  clu x e h = Some p →
  ∃ p', clu (x - y) e h = Some p'. 
induction y; intros. exists p. rewrite <- Minus.minus_n_O. assumption. apply IHy
in H. destruct H. generalize dependent p. generalize dependent e. generalize
dependent h. generalize dependent x0. induction (x - y) eqn:xy; intros. exists x0. rewrite
NPeano.Nat.sub_0_le in xy. apply Le.le_trans with (n:=x) (m:=y) (p:=S y) in xy.
rewrite <- NPeano.Nat.sub_0_le in xy. rewrite xy. assumption. apply Le.le_n_Sn.
apply IHn with (x0:=x0). . assert (x - S y = 0).
destruct y; exists p; assumption. inversion H. destruct (lookup e h) eqn:lue.
destruct c. induction y. simpl. exists p. assumption.
destruct IHy. rewrite inversion H0. destruct y. try (inversion H1).  apply IHx with (y:=y) in H1. . 

Lemma closed_under_inf' : ∀ c c' c'' e x Ψ Φ, closed_under c (Φ ++ x ↦ cl c' e :: Ψ) →
  closed_under c (Φ ++ x ↦ cl c'' e :: Ψ).
intros. unfold closed_under. unfold closed_under in H. destruct c.  
apply forevery_impl with (p:=(λ x0 : nat,
       ∃ (e' : nat) (c'0 : closure),
       clu x0 clos_env0 (Φ ++ x ↦  cl c' e :: Ψ) = Some (e' ↦ c'0))). 
intros. destruct H0. destruct H0. apply clu_inf with
(c':=c'') in H0. destruct H0. destruct x2. exists x0, (close
clos_tm1 clos_env1).  assumption. assumption. Qed.

Lemma closed_under_inf_eq : ∀ c c' c'' e x Ψ Φ, closed_under c (Φ ++ x ↦ cl c' e :: Ψ) 
  ↔ closed_under c (Φ ++ x ↦ cl c''  e :: Ψ).
split; apply closed_under_inf'. Qed.

Lemma well_formed_heap_has_unique_domain : ∀ h, well_formed_heap h → unique (domain h).
intros. induction h. apply unil. destruct a. simpl. apply ucons. simpl in H.
destruct c. destruct H. destruct H0.  assumption. apply IHh. destruct c.
destruct H. destruct H0.  assumption. Qed. 

Lemma clu_cons : ∀ c c' x ne ne' xs f,
  isfresh (domain xs) f →
  clu x ne xs = Some c → 
  clu x ne (f↦cl c' ne'::xs) = Some c.
intros c c' x. induction x; intros. simpl in H0. remember (lookup ne xs). destruct
o. destruct c0. symmetry in Heqo. assert (lu:=Heqo). apply (ex_intro (λ x, lookup ne xs = Some x)
(cl c0 n)) in Heqo. simpl. unfold lookup. simpl. destruct (eq_nat_dec ne f).
subst. destruct Heqo. apply lookup_domain in H1. apply H in H1. inversion H1. rewrite
<- beq_nat_false_iff in n0. rewrite n0.  unfold lookup in lu. rewrite lu.
assumption. inversion H0. destruct (eq_nat_dec ne f). subst. simpl in H0.
remember (lookup f xs). destruct o. symmetry in Heqo. assert (lu:=Heqo). apply
(ex_intro (λ x, lookup f xs = Some x) c0) in Heqo. destruct Heqo. apply lookup_domain in
H1. apply H in H1. inversion H1. inversion H0. simpl. unfold lookup.
rewrite <- beq_nat_false_iff in n. simpl. rewrite n. simpl in H0. unfold lookup
in H0. destruct (find (λ p : nat * cell, beq_nat ne (fst p)) xs). destruct p.
destruct c0. apply IHx. assumption. assumption. inversion H0. Qed.

Lemma clu_under_weaken : ∀ h h' c ne x, 
  unique (domain (h ++ h')) → 
  clu x ne h = Some c → 
  clu x ne (h' ++ h) = Some c. 
intros. induction h'. auto. destruct a. destruct c0. simpl. apply clu_cons.
rewrite domain_app in H. apply unique_app in H. simpl in H. inversion H. subst.
unfold isfresh. rewrite domain_app. assumption. apply IHh'. rewrite domain_app
in H. apply unique_app in H. simpl in H. inversion H. subst. rewrite domain_app.
apply unique_app.  assumption. Qed. 

Lemma clu_app : ∀ Φ Ψ x e, unique (domain (Φ ++ Ψ)) → clu x e (Φ ++ Ψ) = clu x e (Ψ ++ Φ). 
intros Φ Ψ. induction x; intros. 
- simpl. rewrite lookup_app_unique. reflexivity. assumption.
- simpl. rewrite lookup_app_unique. destruct (lookup e (Ψ ++ Φ)).
  destruct c. rewrite IHx. reflexivity. assumption. reflexivity. assumption.
  Qed.   

Lemma closed_under_weaken : ∀ h h' c, 
  unique (domain (h ++ h')) → 
  closed_under c h → 
  closed_under c (h' ++ h).  intros. induction h'. 
- auto. 
- destruct a. simpl. unfold closed_under. destruct c.  simpl in *. rewrite
  for_in_iff. rewrite for_in_iff in H0. rewrite unique_domain_app in H.
  inversion H. subst. rewrite unique_domain_app in H4. apply IHh' in H4. rewrite
  for_in_iff in H4. intros. specialize (H4 x H1). destruct H4. destruct H2.
  exists x0, x1. destruct c0. apply clu_cons. assumption. assumption. Qed. 

Lemma unique_weaken_app {A} : ∀ h h' : list A, unique (h ++ h') → unique h'. 
intros. induction h. auto. inversion H. auto. Qed. 

Lemma well_formed_inf' : ∀ Φ Ψ x c c' n Υ,
  well_formed (⟨Φ & x ↦ cl c' n, Ψ, Υ⟩c) →
  well_formed (⟨Φ, x ↦ cl c n, Ψ & Υ⟩c).
intros. split.  inversion H. apply closed_under_weaken.  unfold closed_under.
rewrite domain_app. apply unique_app. apply well_formed_heap_has_unique_domain
in H1. repeat (rewrite <- app_assoc in H1). simpl in H1.  rewrite domain_app in
H1. apply unique_weaken_app in H1. rewrite domain_inf with (m':=cl c n) in H1.
rewrite <- domain_app. assumption. assert (x ↦ cl c n :: Φ = [x ↦ cl c n] ++ Φ)
by reflexivity. rewrite H2. apply closed_under_weaken; try auto. clear H2.
apply well_formed_heap_has_unique_domain in H1. rewrite unique_domain_app.
repeat (rewrite <- app_assoc in H1). rewrite domain_app in H1. apply
unique_weaken_app in H1. rewrite domain_app in H1. apply unique_weaken_app in
H1. assumption. inversion H. repeat (rewrite <- app_assoc in H1). simpl in H1.
set (h := Υ ++ Ψ). assert (h = Υ ++ Ψ) by reflexivity. rewrite app_assoc.
rewrite app_assoc in H1. rewrite <- H2 in *. clear H2. induction h. inversion
H1. destruct H3. split. assumption. auto. simpl. destruct a. simpl in *.
destruct c0. destruct H1. destruct H2. split. unfold isfresh. rewrite domain_inf
with (m':= cl c' n). assumption. split. apply closed_under_inf' with (c':=c').
auto. apply IHh. assumption. Qed. 


Lemma monotonic_heap : ∀ c1 c2, c1 ⇓ c2 → domain (st_heap c1) ⊆ domain (st_heap c2).  
intros c1 c2 step.  induction step; unfold st_heap in *; simpl in *.
- assert (domain (Ψ ++ Υ ++ x ↦ cl {| clos_tm := :λB; clos_env := e |} y :: Φ') = 
          domain (Ψ ++ Υ ++ x ↦ cl M y :: Φ')). apply domain_inf'. rewrite H0.
          repeat (rewrite <- app_assoc in IHstep).  assumption. 
- apply subset_id. 
- apply subset_trans with (ys:=domain(Ψ ++ Φ')). assumption. clear IHstep1.
  rewrite domain_app in IHstep2. apply subset_comm1 in IHstep2.  simpl in
  IHstep2. destruct IHstep2.  apply subset_comm1 in H1. rewrite <- domain_app in
  H1. assumption.
Qed. 


Lemma r_ur_app {A}: ∀ xs ys zs (x:A), xs ++ ys ++ x :: zs = (xs ++ ys ++ [x]) ++ zs. 
intros. repeat (rewrite <- app_assoc). reflexivity. Qed. 

Lemma unique_domain_step : ∀ Φ Ψ Ψ' c v, 
  unique (domain (Φ ++ Ψ)) →
  ⟨Ψ & Φ⟩c ⇓ ⟨Ψ' & Φ⟩v  →
  unique (domain (Φ ++ Ψ')). 
intros. induce H0. 
- inversion H2. inversion H3. subst. clear H2 H3 H9. 
  rewrite r_ur_app. rewrite r_ur_app in H1.  specialize (IHstep _ _ _ _ _ H1
  eq_refl eq_refl). rewrite <- r_ur_app. rewrite app_assoc. rewrite domain_inf
  with (m':=cl M y). rewrite <- app_assoc. rewrite r_ur_app. assumption. 
- inversion H2. inversion H3. subst. subst. auto. 
- inversion H2. inversion H3. subst. clear H2 H3 H8. 
  specialize (IHstep1 Φ0 Ψ0 Φ' _ _ H0 eq_refl eq_refl). 
  destruct H. unfold isfresh in x. clear H. rewrite domain_app in x. rewrite
  in_app_iff in x. rewrite or_comm in x. rewrite <- in_app_iff in x. rewrite
  domain_app in IHstep1. apply unique_app in IHstep1. 
  apply (@ucons _ f (domain Φ' ++ domain Φ0) x) in IHstep1. 
  specialize (IHstep2 Φ0 (f ↦ cl (close N e) ne :: Φ') Ψ' (close B f) (close
  (:λB') ae)). rewrite unique_domain_app in IHstep2. simpl in IHstep2. rewrite
  domain_app in IHstep2. specialize (IHstep2 IHstep1 eq_refl eq_refl).
  assumption. Qed.

Lemma clu_monotonic : ∀ Ψ x e c v l cl Ψ' Υ, 
  unique (domain (Υ ++ Ψ)) →
  clu x e (Υ ++ Ψ)  = Some (l,cl) →
  ⟨Ψ & Υ⟩c ⇓ ⟨Ψ' & Υ⟩v  →
  ∃ cl', clu x e (Υ ++ Ψ')  = Some (l, cl').
intros. induce H1. 
- inversion H3. inversion H4. subst. clear H3 H4 H10. specialize (IHstep Φ x0 e0
  M (close (:λB) e) l cl0 Φ' (Υ0 ++ Υ ++ [x ↦ cl M y])). assert (Υ0 ++ Υ ++ x ↦
  cl M y :: Φ = (Υ0 ++ Υ ++ [x ↦ cl M y]) ++ Φ). repeat (rewrite <- app_assoc).
  reflexivity. rewrite H3 in H2. rewrite r_ur_app in H0. specialize (IHstep H0 H2 eq_refl eq_refl).
  destruct IHstep. repeat (rewrite <- app_assoc in H4). simpl in H4. rewrite
  app_assoc in H4.  apply clu_inf with (c':=close (:λB) e) in H4. rewrite <-
  app_assoc in H4. assumption. 
- inversion H3. inversion H4. subst. subst. exists cl0. auto. 
- inversion H3. inversion H4. subst. clear H3 H4 H9. 
  specialize (IHstep1 _ _ _ _ _ _ _ _ _ H0 H1 eq_refl eq_refl). destruct IHstep1.
  apply unique_domain_step in H1_; auto. destruct H. clear H. unfold isfresh in
  x1. rewrite domain_app in x1.  rewrite in_app_iff in x1. rewrite or_comm in
  x1. rewrite <- in_app_iff in x1.  rewrite domain_app in H1_. apply unique_app
  in H1_.  apply (@ucons _ f (domain Φ' ++ domain Υ0) x1) in H1_.  rewrite
  clu_app in H2. apply clu_cons with (c':=close N e) (ne':=ne) (f:=f) in H2.
  rewrite app_comm_cons in H1_.  refine (IHstep2 _ _ _ _ _ _ _ _ _ _ _ eq_refl
  eq_refl). rewrite unique_domain_app. simpl. simpl in H1_. rewrite <-
  domain_app in H1_.  assumption. rewrite clu_app. simpl. apply H2. rewrite
  unique_domain_app.  simpl. simpl in H1_. rewrite <- domain_app in H1_.
  assumption. unfold isfresh.  rewrite domain_app. assumption. inversion H1_.
  subst. rewrite domain_app.  apply unique_app. assumption. Qed. 

Definition linkage : heap → Map nat nat := map (λ x, match x with 
  | (x, cl _ l) => (x, l) 
  end).

Lemma domain_linkage : ∀ x h, In x (domain h) → ∃ y, In (x,y) (linkage h).
intros. induction h. inversion H. destruct a. simpl in H. inversion H.  subst.
destruct c. exists n. simpl. auto. simpl. destruct c. apply IHh in H0. destruct
H0. exists x0. auto. Qed. 

Lemma linkage_domain : ∀ x y h, In (x,y) (linkage h) → In x (domain h). 
intros. induction h. inversion H. destruct a. destruct c. inversion H. inversion
H0. subst. simpl. auto. simpl. auto. Qed. 

Lemma linkage_monotonic_reachable : ∀ Φ Φ' Υ c v,
  ⟨Φ & Υ⟩c ⇓ ⟨Φ' & Υ⟩v  →
  linkage Φ ⊆ linkage Φ'. 
intros. induce H. 
- inversion H1. inversion H2. subst. clear H1 H2 H8. 
  unfold linkage. rewrite map_app. rewrite map_app. apply subset_comm2. apply
  subset_comm1. simpl. split. auto. apply subset_cons. apply subset_comm1. apply
  subset_comm2. apply subset_app_id.  eapply IHstep; reflexivity. 
- inversion H1. inversion H2. subst. subst. apply subset_id. 
- inversion H2. inversion H3. subst. clear H2 H3 H9. apply subset_trans with
  (ys:=linkage (f↦cl (close N e) ne::Φ')). simpl. apply subset_cons. eapply
  IHstep1; try reflexivity. eapply IHstep2; try reflexivity. 
Qed. 

Lemma linkage_lookup : ∀ Φ x n, 
  unique (domain Φ) → 
  In (x ↦ n) (linkage Φ) → 
  ∃ c, lookup x Φ = Some (cl c n). 
intros.  induction Φ. inversion H0. destruct a. destruct c. inversion H. subst.
inversion H0. inversion H1. subst. exists c. apply linkage_domain in H0. apply
in_domain_lookup in H0. destruct H0. assert (e':=e). unfold lookup in e. unfold
find in e. simpl in e. rewrite <- beq_nat_refl in e. inversion e. subst.
assumption. unfold lookup. unfold find. simpl. destruct (beq_nat x n0) eqn:ben.
apply beq_nat_true in ben. subst. apply linkage_domain in H1. apply H3 in H1.
inversion H1. apply IHΦ. assumption. assumption. Qed. 

Lemma lookup_in {a} : ∀ (Φ:Map nat a) x y,
  lookup x Φ = Some y →
  In (x, y) Φ. 
intros. induction Φ. inversion H. simpl. unfold lookup in H. unfold find in H.
simpl in H. destruct a0. simpl in H. destruct (beq_nat x n) eqn:ben. inversion
H. subst. apply beq_nat_true in ben. subst. auto. apply IHΦ in H. auto. Qed. 

Lemma lookup_linkage : ∀ Φ x n c,
  lookup x Φ = Some (cl c n) →
  In (x ↦ n) (linkage Φ). 
intros. apply lookup_in in H. unfold linkage. rewrite in_map_iff. exists (x ↦ cl
c n). auto. Qed. 

Lemma linkage_lu : ∀ Φ Φ' x c n,
  unique (domain Φ') →
  linkage Φ ⊆ linkage Φ' → 
  lookup x Φ = Some (cl c n) →
  ∃ c', lookup x Φ' = Some (cl c' n).
intros. apply lookup_linkage in H1. rewrite <- subset_eq in H0. apply H0 in H1.
apply linkage_lookup in H1. assumption. assumption. Qed.

Lemma clu_luf : ∀ x e c Φ, 
  clu x e Φ = Some c →
  ∃ x, lookup e Φ = Some x. 
intros. destruct x; simpl in H; destruct (lookup e Φ). exists c0. reflexivity.
inversion H. exists c0. reflexivity. inversion H. Qed. 

Lemma clu_zero : ∀ e l c Φ,
  clu 0 e Φ = Some (l, c) →
  e = l ∧ ∃ n, lookup l Φ = Some (cl c n) .
intros. inversion H. destruct (lookup e Φ) eqn:lue. destruct c0 eqn:c0e.
inversion H1. rewrite <- H3. rewrite H2 in *. rewrite lue. split; auto. exists
n. auto. inversion H1. Qed. 

Lemma clu_succ : ∀ x e l c Φ,
  clu (S x) e Φ = Some (l, c) → 
  ∃ e' c', lookup e Φ = Some (cl c' e') ∧ 
  clu x e' Φ = Some (l, c). 
intros. simpl in H. destruct (lookup e Φ) eqn:lue. destruct c0 eqn:c0e. exists
n, c1. auto. inversion H. Qed. 

Lemma linkage_clu : ∀ Φ Φ' x e l cl, 
  unique (domain Φ') →
  linkage Φ ⊆ linkage Φ' → 
  clu x e Φ = Some (l, cl) →
  ∃ cl', clu x e Φ' = Some (l, cl').
intros. rewrite <- subset_eq in H0. generalize dependent e.
induction x; intros.  
- simpl. apply clu_zero in H1. destruct H1. destruct H2. subst. apply
  lookup_linkage in H2. apply H0 in H2. apply linkage_lookup in H2. destruct H2.
  rewrite H1. exists x0. reflexivity. assumption. 
- assert (H1':=H1). apply clu_succ in H1. destruct H1. destruct H1. destruct H1.
  apply IHx in H2. destruct H2. apply lookup_linkage in H1. apply H0 in H1.
  apply linkage_lookup in H1. destruct H1. exists x2. simpl. rewrite H1.
  assumption. assumption. 
Qed. 

Lemma well_formed_heap_replace : ∀ Φ Ψ c v e l, 
  well_formed_heap (Φ ++ (l, cl c e) :: Ψ) →
  closed_under v Ψ →
  well_formed_heap (Φ ++ (l, cl v e) :: Ψ).
intros. induction Φ. simpl. inversion H. destruct H2. split; try split; auto.
simpl in H. destruct a. destruct c0. inversion H. destruct H2. apply IHΦ in H3.
split. unfold isfresh. rewrite domain_inf with (m':=cl c e). assumption. split;
auto. destruct H. unfold closed_under. destruct c0. apply in_forevery. intros.
unfold closed_under in H4. destruct H4. rewrite for_in_iff  in H4. specialize
(H4 x H5). destruct H4. destruct H4. eapply linkage_clu in H4. exists x0. apply H4.  
apply well_formed_heap_has_unique_domain. auto. unfold linkage. rewrite map_app.
rewrite map_app. simpl. apply subset_id. Qed.   

Lemma clu_monotonic_reachable : ∀ Ψ x e c v l cl Ψ' Υ, 
  unique (domain (Υ ++ Ψ)) →
  clu x e Ψ  = Some (l,cl) →
  ⟨Ψ & Υ⟩c ⇓ ⟨Ψ' & Υ⟩v  →
  ∃ cl', clu x e Ψ'  = Some (l, cl').
intros. assert (H1':=H1).  apply linkage_monotonic_reachable in H1. eapply linkage_clu in H1; try
auto. apply H1. apply unique_domain_step in H1'. rewrite domain_app in H1'.
apply unique_weaken_app in H1'.  assumption. assumption. apply H0. Qed. 

Lemma closed_under_comm : ∀ h h' c , 
  unique (domain (h ++ h')) →
  closed_under c (h ++ h') → 
  closed_under c (h' ++ h). 
intros. destruct c. simpl in *. rewrite for_in_iff. rewrite for_in_iff in H0.
intros. specialize (H0 x H1). rewrite clu_app in H0; auto. Qed.

Lemma closed_under_cons : ∀ h x c n e,
  isfresh (domain h) x → closed_under c h → closed_under c (x↦cl n e::h). 
intros. unfold closed_under in H0. destruct c. rewrite for_in_iff in H0. unfold
closed_under. rewrite for_in_iff. intros. apply H0 in H1. destruct H1. destruct
H1. exists x1, x2. apply clu_cons. assumption. assumption. Qed. 

Lemma isfresh_comm {a} : ∀ (h h':Map nat a) x, isfresh (domain (h ++ h')) x →
isfresh (domain (h' ++ h)) x.
intros. unfold isfresh. unfold not. intros. rewrite domain_app in H0. rewrite
in_comm in H0. rewrite <- domain_app in H0. apply H in H0. assumption. Qed.  

Lemma isfresh_cons : ∀ h (x:nat) y, isfresh (x::h) y → isfresh h y. 
intros. unfold isfresh. unfold not. intros. apply H. simpl. auto. Qed. 

Lemma well_formed_heap_insert_inf : ∀ Φ f N e Ψ, 
  isfresh (domain (Φ ++ Ψ)) f →
  closed_under N Ψ →
  well_formed_heap (Φ ++ Ψ) →
  well_formed_heap (Φ ++ f ↦ cl N e :: Ψ).
intros. induction Φ. simpl. split; auto. destruct a. destruct c. simpl. split.
inversion H1. unfold isfresh. rewrite domain_app. rewrite in_comm. simpl. unfold
not. intros. destruct H4. apply H. subst. simpl. auto. apply H2. rewrite
domain_app. rewrite in_comm. assumption. assert (well_formed_heap (Φ ++ f ↦ cl N
e :: Ψ)). apply IHΦ. simpl in H. unfold isfresh in H. simpl in H. unfold
isfresh. unfold not. intros. apply H. auto. inversion H1. destruct H3. auto.
split; auto. apply closed_under_comm. rewrite unique_domain_app. apply
well_formed_heap_has_unique_domain. assumption. simpl. apply closed_under_cons.
simpl in H. apply isfresh_comm. apply isfresh_cons in H. assumption. simpl in
H1. destruct H1. destruct H3. apply closed_under_comm. apply
well_formed_heap_has_unique_domain. assumption. assumption. Qed. 

Theorem well_formed_step : ∀ c v, well_formed c → c ⇓ v → well_formed v.
intros. induction H0. 
- apply well_formed_inf in H. apply IHstep in H.  apply well_formed_inf' in H.
  assumption. 
- assumption. 
- apply IHstep2. destruct H. simpl in H. apply forevery_app in H. destruct H.
  specialize (IHstep1 (conj H H1)). split. clear H H2 H1 IHstep2 H0_
  H0_0. unfold closed_under. simpl. destruct IHstep1. unfold closed_under in H.
  rewrite for_in_iff in *. rewrite for_in_iff in H. intros. simpl in H. 
  destruct x. unfold clu. unfold lookup. simpl. rewrite <- beq_nat_refl.  exists
  f, (close N e). split; auto. specialize (H x). destruct H. assert (x =
  Peano.next (S x)). auto. rewrite H.  apply in_map. rewrite remove_not_in.
  apply H2. auto. destruct H. unfold clu. unfold lookup. simpl.  rewrite <-
  beq_nat_refl. unfold clu in H. exists x0, x1. apply clu_cons. destruct H0.
  unfold isfresh in x2. unfold isfresh. unfold not.  intros. apply x2.  rewrite
  domain_app. rewrite in_app_iff. auto. assumption.  clear IHstep2. clear H.
  apply well_formed_heap_has_unique_domain in H1. clear H0_0. rewrite for_in_iff
  in H2. destruct H0. clear H. destruct IHstep1. clear H. apply
  well_formed_heap_insert_inf; auto. unfold closed_under. rewrite for_in_iff.
  intros. apply H2 in H.  destruct H. destruct H. exists x1. eapply
  clu_monotonic_reachable. apply H1. apply H. apply H0_.  
Qed. 

Lemma values_only : ∀ c e M Φ Ψ, c ⇓ ⟨Ψ & Φ⟩close M e → value M.
intros. inversion H; simpl; constructor. Qed.

