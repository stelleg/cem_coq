Require Import db util.
Require Import Arith.EqNat.
Require Import List Unicode.Utf8 Arith.Peano_dec Basics.
Require Import CpdtTactics.

Definition append := Datatypes.app.

Record closure : Type := close {
  clos_tm : tm;
  clos_env : nat
}.

Inductive cell : Type :=
  | cl : closure → nat → cell.

Definition clclose (c: cell) : closure := match c with cl c e => c end.

Definition heap := Map nat cell.

Record configuration : Type := conf {
  st_heap : heap;
  st_clos : closure
}.

Definition I (e : tm) : configuration := conf nil (close e 0).

Notation " x ↦ M " := (x, M) (at level 40).
Notation " ⟨ Φ ⟩ m " := (conf Φ m) (at level 40).
Notation " ⟨ Ψ , b ⟩ N " := (conf (cons b Ψ) N) (at level 40).
Notation " ⟨ Φ , b , Ψ ⟩ N " := (conf (append _ Ψ (cons b Φ)) N) (at level 40).
Notation " { M , e } " := (cl M e).
Notation " < M , e > " := (close M e).

(* cactus lookup: lookup deBruijn index i at location x in heap h yields
location y *)
Inductive cactus_lookup : nat → nat → heap → nat → Prop :=
  | zero : forall x Φ M Υ, cactus_lookup 0 x (Φ ++ (x ↦ M) :: Υ) x
  | pred : forall x y z Φ M Υ i, cactus_lookup i x Φ z → 
            cactus_lookup (S i) y (Φ ++ (y ↦ {M, x}):: Υ) z.

Fixpoint clu (v env:nat) (h:heap) : option (nat * closure) := match lookup env h with
  | None => None
  | Some (cl c a) => match v with
    | S n => clu n a h
    | 0 => Some (env, c)
    end
  end.

Definition closed_under (c : closure) (h : heap)  : Prop := match c with
  | close t e => forevery (fvs t) 
      (λ x, ∃e' c', clu x e h = Some (e',c') ∧ In e' (domain h))
  end.

Definition closed (t : tm) : Prop := closed_under (close t 0) nil.

Definition well_formed_heap (h : heap) : Prop := forevery h 
  (λ x, match x with | (v,cl c e') => closed_under c h end). 

Definition well_formed (c : configuration) : Prop := match c with 
  | conf h t => closed_under t h ∧ well_formed_heap h ∧ unique (domain h)
  end.

Reserved Notation " c1 '⇓' c2 " (at level 50).
Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M B x y z Φ Ψ Υ v e, clu v z (Υ ++ x ↦ {M,y} :: Φ) = Some (x, M) → 
            ⟨Φ, (x ↦ {M,y}), Υ⟩M ⇓ ⟨Ψ, (x ↦ {M,y}), Υ⟩close (:λB) e →
    ⟨Φ, x ↦ {M, y}, Υ⟩close (var v) z ⇓ ⟨Ψ, x ↦ {close (:λB) e, y}, Υ⟩close (:λB) e
  | Abs : ∀ N Φ e, ⟨Φ⟩close (:λN) e ⇓ ⟨Φ⟩close (:λN) e
  | App : ∀ N M B B' Φ Ψ Υ f e ne ae, 
                  fresh' f Ψ → 
          ⟨Φ⟩close M e ⇓ ⟨Ψ⟩close (:λB) ne → 
      ⟨Ψ, f ↦ {close N e, ne}⟩close B f ⇓ ⟨Υ⟩close (:λB') ae   →
              ⟨Φ⟩close (M@N) e ⇓ ⟨Υ⟩close (:λB') ae
where " c1 '⇓' c2 " := (step c1 c2).

Definition configuration' := sig well_formed.
Definition step' (c1 c2: configuration') : Prop := match (c1, c2) with
  | (exist c1 _, exist c2 _) => step c1 c2 end.

Lemma well_formed_inf : ∀ c x c' n  Φ Υ, 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c) → 
  well_formed (⟨Φ, x ↦ cl c' n, Υ⟩c').
intros. split. inversion H. destruct H1. unfold well_formed_heap in H1. apply
forevery_app in H1.  destruct H1. simpl in H3. destruct H3. auto. split;
destruct H; destruct H0; auto. Qed.

Lemma forevery_cons {A} : ∀ (p:A→Prop) (x:A) xs, p x → forevery xs p → forevery (x::xs) p. 
intros. simpl. split; assumption. Qed. 

Lemma clu_inf : ∀ x x' c c' e e'  Ψ Φ clo n, 
  clu x e (Φ ++ x' ↦ cl c e' :: Ψ) = Some (n, clo) →
  ∃ clo', clu x e (Φ ++ x' ↦ cl c' e' :: Ψ) = Some (n, clo').
intros x. induction x. intros. simpl in H. remember (lookup e (Φ ++ x' ↦ cl c e' :: Ψ)).
simpl. destruct o. symmetry in Heqo. apply (ex_intro (λ x, lookup e (Φ ++ x' ↦ cl
c e' :: Ψ) = Some x) c0) in Heqo. apply lookup_in_domain in Heqo. rewrite
domain_inf with (m':= cl c' e') in Heqo. apply in_domain_lookup in Heqo.
destruct Heqo. rewrite H0. destruct x. destruct c0. inversion H. subst. clear H.
exists c1. reflexivity. inversion H. intros. specialize (IHx x' c c').
simpl in H. remember (lookup e (Φ ++ x' ↦  cl c e' :: Ψ)). destruct o.  destruct
c0. specialize (IHx n0 e' Ψ Φ clo n H). destruct IHx. simpl. remember (lookup e (Φ ++
x' ↦ cl c' e' :: Ψ)). destruct o. destruct c1. assert (n1 = n0). clear H0. clear
H. induction Φ.  simpl in Heqo. simpl in Heqo0. unfold lookup in Heqo. unfold
lookup in Heqo0.  simpl in Heqo. simpl in Heqo0. destruct (beq_nat e x').
inversion Heqo. subst.  inversion Heqo0. subst. reflexivity. rewrite <- Heqo in
Heqo0.  inversion Heqo0.  subst. reflexivity. destruct a. unfold lookup in Heqo.
unfold lookup in Heqo0. simpl in Heqo. simpl in Heqo0. destruct (beq_nat e n2). 
rewrite <- Heqo in Heqo0. inversion Heqo0. subst. reflexivity. simpl in Heqo.
simpl in Heqo0. apply IHΦ. assumption. assumption. subst. exists x0. assumption. symmetry
in Heqo. apply (ex_intro (λ x, lookup e (Φ ++ x' ↦ cl c e' :: Ψ) = Some x) (cl
c0 n0)) in Heqo. apply lookup_in_domain in Heqo. rewrite domain_inf with (m':=cl
c' e') in Heqo. apply in_domain_lookup in Heqo. destruct Heqo. rewrite H1 in
Heqo0. inversion Heqo0. inversion H. Qed. 

Lemma closed_under_inf' : ∀ c c' c'' e x Ψ Φ, closed_under c (Φ ++ x ↦ {c', e} :: Ψ) →
  closed_under c (Φ ++ x ↦ {c'', e} :: Ψ).
intros. unfold closed_under. unfold closed_under in H. destruct c.  
apply forevery_impl with (p:=(λ x0 : nat,
       ∃ (e' : nat) (c'0 : closure),
       clu x0 clos_env0 (Φ ++ x ↦ {c', e} :: Ψ) = Some (e' ↦ c'0)
       ∧ In e' (domain (Φ ++ x ↦ {c', e} :: Ψ)))). 
intros. destruct H0. destruct H0. destruct H0. apply clu_inf with
(c':=c'') in H0. destruct H0. destruct x2. exists x0, (close
clos_tm1 clos_env1). split. assumption.  rewrite domain_inf with (m':=cl c' e).
assumption. assumption. Qed.

Lemma well_formed_inf' : ∀ Φ Ψ x c c' n,
  well_formed (⟨Φ, x ↦ cl c' n, Ψ⟩c) →
  well_formed (⟨Φ, x ↦ cl c n, Ψ⟩c).
intros. split.  inversion H. apply closed_under_inf' with (c':=c'). assumption.
split. destruct H. destruct H0. apply forevery_app in H0. destruct H0. simpl in H2.
destruct H2. rename x into X. apply forevery_cons with (x:=X ↦ {c, n}) (xs:=Φ)
in H3; try assumption. assert (h' := conj H0 H3). rewrite <- forevery_app in h'.
clear H3 H0. apply forevery_impl with (p:=(λ x : nat * cell,
        let (_, c0) := x in
        match c0 with
        | {c1, _} =>
            closed_under c1 (append (nat * cell) Ψ (X ↦ {c', n} :: Φ))
        end)).
intros.
destruct a. destruct c0. apply closed_under_inf' with (c':=c'). assumption.
assumption. destruct H. destruct H0. rewrite domain_inf with (m':=cl c' n).
assumption. Qed.

Lemma clu_cons : ∀ c c' x ne ne' xs f,
  fresh' f xs →
  clu x ne xs = Some c → 
  clu x ne (f↦cl c' ne'::xs) = Some c.
intros c c' x. induction x; intros. simpl in H0. remember (lookup ne xs). destruct
o. destruct c0. symmetry in Heqo. assert (lu:=Heqo). apply (ex_intro (λ x, lookup ne xs = Some x)
(cl c0 n)) in Heqo. simpl. unfold lookup. simpl. destruct (eq_nat_dec ne f).
subst. apply lookup_in_domain in Heqo. apply H in Heqo. inversion Heqo. rewrite
<- beq_nat_false_iff in n0. rewrite n0.  unfold lookup in lu. rewrite lu.
assumption. inversion H0. destruct (eq_nat_dec ne f). subst. simpl in H0.
remember (lookup f xs). destruct o. symmetry in Heqo. assert (lu:=Heqo). apply
(ex_intro (λ x, lookup f xs = Some x) c0) in Heqo. apply lookup_in_domain in
Heqo. apply H in Heqo. inversion Heqo. inversion H0. simpl. unfold lookup.
rewrite <- beq_nat_false_iff in n. simpl. rewrite n. simpl in H0. unfold lookup
in H0. destruct (find (λ p : nat * cell, beq_nat ne (fst p)) xs). destruct p.
destruct c0. apply IHx. assumption. assumption. inversion H0. Qed.

Lemma clu_monotonic : ∀ Φ Ψ x e c v l cl, 
  clu x e Φ = Some (l,cl) →
  ⟨Φ⟩c ⇓ ⟨Ψ⟩v  →
  ∃ cl', clu x e Ψ = Some (l, cl').
intros. remember (conf Φ c). remember (conf Ψ v). generalize dependent c.
generalize dependent v. generalize dependent l. generalize dependent cl0.
generalize dependent x. generalize dependent Φ. generalize dependent Ψ.
generalize dependent e. induction H0; intros. inversion Heqc0. inversion
Heqc1. subst. specialize (IHstep e0 (Υ ++ x ↦ {M, y} :: Ψ) (Υ ++
x ↦ {M, y} :: Φ) x0 cl0 l H1 (close (lam B) e) eq_refl M eq_refl). destruct
IHstep. apply clu_inf with (c':=close (lam B) e) in H2. assumption. 
inversion Heqc1. inversion Heqc0. subst. inversion Heqc0. subst. exists cl0.
assumption. inversion Heqc1. subst. inversion Heqc0. subst. clear Heqc1. clear
Heqc0. apply IHstep1 with (Ψ0:=Ψ)(v:=close (lam B) ne) (c:= close M e) in
H0; try reflexivity. destruct H0. apply IHstep2 with (Φ:=f↦(cl (close N e)
ne)::Ψ) (cl0:=x0) (c:=close B f) (v:=close (lam B') ae). apply clu_cons.
assumption. assumption. reflexivity. reflexivity. Qed. 

Lemma monotonic_heap : ∀ c1 c2, c1 ⇓ c2 → domain (st_heap c1) ⊆ domain (st_heap c2).  
intros c1 c2 step.  induction step. simpl. simpl in IHstep. 
unfold domain at 2. unfold domain at 2 in IHstep. rewrite map_app. rewrite
map_app in IHstep.  simpl. simpl in IHstep. assumption. 
apply subset_id. simpl. simpl in IHstep1. simpl in IHstep2. destruct IHstep2. 
apply subset_trans with (ys:=domain Ψ). assumption. assumption. Qed.

Theorem well_formed_step : ∀ c v, well_formed c → c ⇓ v → well_formed v.
intros. induction H0. apply well_formed_inf in H. apply IHstep in H.  
apply well_formed_inf' in H. assumption. assumption. apply IHstep2. destruct H.
simpl in H. apply forevery_app in H. destruct H. specialize (IHstep1 (conj H
H1)). split; try split. clear H H2 H1 IHstep2 H0_ H0_0. destruct IHstep1.
destruct H1. simpl. simpl in H. rewrite forevery_map in H. induction (fvs B).
simpl.  auto. destruct a. simpl in H. apply IHl in H. simpl. split; try
assumption.  unfold lookup. simpl. rewrite <- beq_nat_refl. exists f, (close N
e). split; auto. simpl. simpl in H. destruct H. split; try (apply IHl;
assumption). unfold compose in H. simpl in H.  unfold lookup. simpl. rewrite <-
beq_nat_refl.  destruct H. destruct H. exists x , x0. destruct H. split; auto.
apply clu_cons; assumption. unfold well_formed_heap. simpl. split. apply
forevery_impl with (p:=(λ x : nat,
        ∃ (e' : nat) (c' : closure),
        clu x e Φ = Some (e' ↦ c') ∧ In e' (domain Φ))). 
intros. destruct H3.
destruct H3. destruct H3.  apply (clu_monotonic Φ Ψ a e (close M e)
(close (lam B) ne) x x0) in H3. destruct H3. exists x, x1. split. apply
clu_cons.  assumption. assumption. apply or_intror. apply monotonic_heap
in H0_. simpl in H0_. rewrite <- subset_eq in H0_. apply H0_ in H4.
assumption. assumption. assumption. inversion IHstep1. destruct H4. unfold
well_formed_heap in H4. apply forevery_impl with (p:= (λ x : nat * cell,
        let (_, c0) := x in match c0 with
                            | {c, _} => closed_under c Ψ
                            end)). 
intros. destruct a. destruct c. unfold closed_under. destruct c. unfold
closed_under in H6. apply forevery_impl with (p:=(λ x : nat,
        ∃ (e' : nat) (c' : closure),
        clu x clos_env0 Ψ = Some (e' ↦ c') ∧ In e' (domain Ψ))).
intros. destruct H7. destruct H7. destruct H7. exists x, x0. split. apply
clu_cons; assumption. simpl. auto. assumption. assumption. apply ucons. simpl.
destruct H0.  assumption. destruct IHstep1. destruct H4. unfold domain in H5.
assumption. Qed. 
    
Lemma values_only : ∀ c e M Ψ, c ⇓ ⟨Ψ⟩close M e → value M.
intros. inversion H; simpl; constructor. Qed.

