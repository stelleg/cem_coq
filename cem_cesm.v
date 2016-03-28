Require Import cem cesm util.
Require Import Unicode.Utf8.
Require Import relations. 
Require Import List. 

Definition b2s (c : configuration) : stack → state := match c with
  | conf h c => λ s, st h s c end.

Notation " c1 '↦s*' c2 " := (c1 →s* c2 ∧ state_value c2) (at level 30). 

Definition convert_to_cesm (c c' : configuration) : Prop := match (c, c') with
  | (conf h c, conf h' c') => ∀ s, (st h s c) →s* (st h' s c') end.

Lemma cem_cesm : ∀ c v, c ⇓ v → ∀ s, b2s c s →s* b2s v s. 
(* Var *)
intros c v H. induction H. simpl. simpl in IHstep. 
assert (∀ s, step' (st (Υ ++ (x ↦ {M,y} :: Φ)) s (close (db.var v) z)) 
                   (st (Υ ++ (x ↦ {M,y} :: Φ)) (inr x::s) M)).
intros. apply Var'. assumption. 
assert (∀ s, step' (st (Υ ++ x ↦ {M, y} :: Ψ) (inr x :: s) (close (db.lam B) e))
                   (st (Υ ++ x ↦ {close (db.lam B) e, y} :: Ψ) s (close (db.lam B) e)))
.
apply Upd. 
intros. rename y into Y.  
apply t_step with (y:=[Υ ++ x ↦ {M, Y} :: Φ, inr x :: s | M]). auto. 
apply t_step2 with (y:= [Υ ++ x ↦ {M, Y} :: Ψ, inr x :: s | (close (db.lam B) e)]). 
auto. auto.   
(* Lam *)
intros. apply t_refl. 
(* App *)
intros. apply t_step with (y:=b2s (⟨Φ ⟩ close M e) (inl (close N e)::s)). 
apply App'. 
apply refl_trans_clos_app with (y:=b2s (⟨Ψ, f ↦ {close N e, ne} ⟩ close B f) s).
apply t_step2 with (y:=b2s (⟨Ψ ⟩ close (db.lam B) ne) (inl (close N e):: s)).
simpl. rename e into E. rename s into S. destruct H. apply Abs' with (p:=x).
assumption. apply IHstep1. apply IHstep2. Qed. 

Lemma cem_cesm_nf : ∀ c v Φ Ψ, conf Φ c ⇓ conf Ψ v → st Φ nil c ↦s* st Ψ nil v. 
intros. split. apply cem_cesm with (s:=nil) in H. simpl in H. assumption.
inversion H; unfold state_value; split;  try (apply db.val); reflexivity. Qed.

Definition s2b (s : state) : configuration := match s with
  | st h s c => conf h c
  end.

Lemma step_stack_app : ∀ a b z c c' Φ Ψ, st Φ a c →s st Ψ b c'
                                      → st Φ (a++z) c →s st Ψ (b++z) c'. 
intros. inversion H; try constructor. assumption. rename p into P. apply Abs'
with (p:=P). assumption. Qed. 

Lemma step_stack_app' : ∀ a b z c c' Φ Ψ, st Φ (a++z) c →s st Ψ (b++z) c'
                                             → st Φ a c →s st Ψ b c'. 
intros. inversion H; subst. rewrite app_comm_cons in H2. apply app_eq_r in H2.
subst. constructor. rewrite app_comm_cons in H5. apply app_eq_r in H5. subst.
apply Var'. assumption. rewrite app_comm_cons in H2. apply app_eq_r in H2. subst.
apply Abs' with (p:=p). assumption. rewrite app_comm_cons in H5. apply app_eq_r
in H5. subst. constructor. Qed.  

Lemma rtc_step_stack_app : ∀ a b z c c' Φ Ψ, st Φ a c →s* st Ψ b c'
                                    → st Φ (a++z) c →s* st Ψ (b++z) c'. 
intros. remember (st Φ a c). remember (st Ψ b c'). generalize dependent Φ.
generalize dependent Ψ. generalize dependent a. generalize dependent c.
generalize dependent c'. generalize dependent b. generalize dependent z.
induction H; intros; subst. inversion Heqs. subst. apply t_refl. specialize
(IHrefl_trans_clos z0 b c'). inversion H; subst. specialize (IHrefl_trans_clos
(close (db.lam b0) e) s Ψ eq_refl (Φ0 ++ l ↦ (cl (close (db.lam b0) e) e') ::
Υ) eq_refl). apply t_step with (y:=st (Φ0 ++ l ↦ (cl (close (db.lam b0) e) e') ::
Υ) (s++z0) (close (db.lam b0) e)). apply step_stack_app with (z:=z0) in H.
assumption. assumption. apply step_stack_app with (z:=z0) in H. specialize 
(IHrefl_trans_clos c0 (inr l :: a) Ψ eq_refl Φ eq_refl). apply t_step with
(y:=st Φ (inr l :: a ++ z0) c0). assumption. assumption. specialize
(IHrefl_trans_clos (close b0 f) s Ψ eq_refl (f ↦ (cl c0 e) :: Φ) eq_refl). apply
step_stack_app with (z:=z0) in H. apply t_step with (y:=st ((f,cl c0 e) :: Φ) (s
++ z0) (close b0 f)). assumption. assumption. specialize (IHrefl_trans_clos
(close m e) (inl (close n e) :: a) Ψ eq_refl Φ eq_refl). apply step_stack_app
with (z:=z0) in H. apply t_step with (y:=st Φ (inl (close n e) :: a ++ z0)
(close m e)). assumption. assumption. Qed.

(* This is much harder, need induction so that  *) 
Lemma cesm_cem : ∀ Φ c Ψ v, st Φ nil c ↦s* st Ψ nil v  
                             → conf Φ c ⇓ conf Ψ v.
                             Admitted.
(* Induction on steps *)
(*
intros. remember (st Φ nil c). remember (st Ψ nil v).
generalize dependent c.  generalize dependent Φ. generalize dependent v.
generalize dependent Ψ.  destruct H. induction H; intros; subst. inversion
Heqs. subst. inversion H0. inversion H. destruct v. simpl in H3. subst. apply
Abs. specialize (IHrefl_trans_clos H0 Ψ v Φ c). remember
(st Ψ s v). generalize dependent s. generalize dependent H0. generalize
dependent c. generalize dependent Ψ. generalize dependent v. generalize
dependent Φ. rewrite rtc_eq in H1. induction H1; intros; subst. inversion H.
apply cons_neq in H6. inversion H6. symmetry in H6. apply cons_neq in H6.
inversion H6. apply cons_neq in H6. inversion H6. symmetry in H6. apply cons_neq
in H6. inversion H6. rewrite <- rtc_eq in H1. clear IHrefl_trans_clos'. subst. apply induction induction
H1. inversion clear H0.
inversion H; subst. remember (st Ψ nil v). generalize dependent Ψ. induction H1;
intros; subst. inversion H. inversion H0; subst.  inversion H; subst. inversion
generalize dependent v.
rewrite <- 

specialize
(IHrefl_trans_clos H0 Ψ v eq_refl). inversion H; intros; subst. remember (st Φ
(inr l :: nil) c0). remember (st Ψ nil v). generalize
dependent Ψ. generalize dependent c0. generalize dependent l. generalize dependent Φ. generalize
dependent v. generalize dependent v0. generalize dependent H0. generalize dependent e. rewrite rtc_eq in
H1. induction H1; intros; subst. inversion Heqs0. rewrite <- rtc_eq in H1.
remember (st Φ (inr l :: nil) c0). generalize dependent Φ. generalize dependent
c0. induction H1. specialize
(IHrefl_trans_clos H0 v Φ). inversion H0. subst.
 specialize (IHrefl_trans_clos Ψ v).
inversion Heqs. 
sbuispecialize
(IHrefl_trans_clos Φ c0). remember 

inversion H0. inversion H2. destruct v.
simpl in H5. subst. specialize IHrefl_trans_clos with (v0:=v).  
intros. inversion H. subst. inversion H1. destruct v. simpl. destruct
st_closure. simpl in H3. subst. apply Abs. subst. rewrite rtc_eq in H3. 
induction H3. inversion H2. subst. simpl. simpl in H0.
symmetry in H0. apply l_cons_neq in H0. inversion H0. simpl. subst. simpl in H0.
apply l_cons_neq in H0. inversion H0. subst. simpl in H0. symmetry in H0. apply
l_cons_neq in H0. inversion H0. subst. simpl in H0. apply l_cons_neq in H0.
inversion H0. subst.  destruct st_closure. inversion H1. simpl in H5. subst.
clear H1. clear H3.  simpl in H2. subst. simpl in H0. apply Abs. rewrite rtc_eq
in H2. destruct H2.  subst. 

subst.induction H. destruct x. destruct
st_closure. simpl in H0. inversion H1. destruct H. inversion H2. simpl in H. simpl. inversion H. subst. apply Abs. 


Lemma cesm_nil : ∀ c v, c →s* v → st_stack c = nil → st_stack v = nil 
      → ∀ s, (st (st_heap c) s (st_closure c)) →s* (st (st_heap v) s (st_closure v)).
intros. inversion H. subst. apply t_refl. rewrite rtc_eq in H3. destruct H3. inversion
H2. subst. simpl in H0. inversion H0. subst. simpl in H1. inversion H1. subst.
simpl in H0. inversion H0. subst. simpl in H1. inversion H1. rewrite <- rtc_eq
in H3. destruct c. destruct z0. simpl in H0. simpl in H1. subst.  simpl.

destruct x0. destruct y. inversion H2. subst. inversion H3. subst. induction s. subst. destruct c. destruct z0. simpl. simpl in H0. simpl in
H1. subst. assumption. subst. 
duction H3. subst. apply t_step. subst. apply inversion H1. 

                                                ↔ 
                                          twostep c v.
intros. split; intros. induction H. induction H. apply ts_refl. 
:

Lemma push_lam : ∀ xs ys, state Φ nil c →s state 



assumption. 
destruct z.
destruct simpl in
IHrefl_trans_clos. induction H. 
simpl. simpl in
induction H. 
destruct x. destruct H. destruct H. induction H. destruct x. simpl in H.  destruct st_closure. destruct clos_tm.
inversion H0. apply cem.Abs. inversion H0. destruct H. 
destruct H. destruct x. destruct c. destruct t. simpl in
H0. destruct H1. clear H0. apply  
H1. splitinversion x. inversion H2. inversion H3. unfold normal_form in H0. induction H. destruct c. simpl in H1. symmetry in H1. apply l_cons_neq in
H1. inversion H1. simpl in H1. apply l_cons_neq in H1. inversion H1. simpl in
H1. symmetry in H1. apply l_cons_neq in H1. inversion H1. simpl in H1. apply
l_cons_neq in H1. inversion H1. induction j
*)

