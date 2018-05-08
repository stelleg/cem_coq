Require Import List curien cem_name util Unicode.Utf8.

Inductive env_eq (h : heap) : curien.env → cem.env → Type := 
  | env_eq_nil : ∀ l, env_eq h nil l
  | env_eq_cons : ∀ t e e' l l' l'', 
      lookup l h = Some (cl (cem.close t l') l'') → 
      env_eq h e l' → 
      env_eq h e' l'' → 
      env_eq h (curien.close t e :: e') l
  .

Inductive close_eq (h : heap) : curien.closure → cem.closure → Type := 
  | close_equiv : ∀ t e l, env_eq h e l → close_eq h (curien.close t e) (cem.close t l).

Lemma nth_lookup : ∀ x h e l c, env_eq h e l → nth_error e x = Some c → 
  sigT (λ l', sigT (λ c', prod (clu x l h = Some (l', c')) (close_eq h c (cell_cl c')))). 
induction x; intros. 
-  inversion H0. subst. unfold clu. inversion H. subst. inversion H2. subst. exists l.
   exists (cl (close t l') l''). split; auto. rewrite H1. reflexivity.
   inversion H2. subst. apply close_equiv.  assumption.  
-  inversion H0. subst. inversion H. subst. inversion H2. subst. apply IHx with
   (c:=c) in H4.  destruct H4. destruct s. exists x0. exists x1. simpl. rewrite
   H1. assumption. assumption. 
Qed. 

Lemma env_eq_fresh : ∀ x c h e l, env_eq h e l → x ∉ domain h → env_eq ((x,c)::h) e l. 
intros. induce H; intros. constructor. apply env_eq_cons with (l':=l')
(l'':=l''). unfold lookup. simpl.  destruct (PeanoNat.Nat.eqb l x) eqn:elx.
symmetry in elx. apply EqNat.beq_nat_eq in elx. subst. apply lookup_domain in
e0. apply H1 in e0.  inversion e0. unfold lookup in e0. assumption. apply
IHenv_eq1. assumption. apply IHenv_eq2. assumption. 
Qed.

Lemma env_eq_step : ∀ h h' c v e l, cem_name.step (conf h c) (conf h' v) → env_eq h e l → env_eq h' e l.
intros. induce X. 
- invert H2. invert H1. apply IHX with (h0:=h) (c:=M) (v:=v0); auto. 
- invert H2. invert H1. assumption. 
- invert H2. invert H1. specialize (IHX _ _ _ _ e0 l H eq_refl eq_refl). apply
  env_eq_fresh with (x:=earg (fresh (domain Ψ))) (c:=cl (close N e) ne) in IHX.
  simpl in *. specialize (X0 _ _ _ _ e0 l IHX eq_refl eq_refl). assumption.
  simpl in *. destruct (fresh (domain Ψ)). simpl. assumption. Qed.

Theorem step_eq : ∀ h c c' v, close_eq h c c' → curien.step c v → 
  sigT (λ co, match co with conf h' v' => prod (cem_name.step (conf h c') co) (close_eq h' v v') end). 
intros. induce H0; intros. 
- exists (conf h c'). inversion H. subst. split. constructor. assumption. 
- destruct c'. inversion H. subst. apply (nth_lookup x h e cl_en c H2) in e0. 
  destruct e0. destruct s. destruct p. destruct x1. specialize (IHstep h
  cell_cl c0). destruct IHstep. destruct x1. destruct y. apply Id with
  (Ψ:=conf_h) (v:=conf_c) in e0.  exists (conf conf_h conf_c). split; auto.
  assumption. 
- inversion H. subst.  specialize (IHstep1 h (close m l)). destruct IHstep1.
  constructor; auto.  destruct x.  destruct y. inversion c. subst.
  specialize (IHstep2 (((earg (fresh (domain conf_h))), cl (close n l)
  l0)::conf_h) (close b (earg (fresh (domain conf_h))))). destruct
  IHstep2. constructor. apply env_eq_cons with (l':=l) (l'':=l0). unfold lookup.
  simpl. rewrite PeanoNat.Nat.eqb_refl.  reflexivity. apply env_eq_fresh. apply
  env_eq_step with (h:=h) (c:=close m l) (v:=close (db.lam b) l0). assumption.
  assumption. destruct (fresh (domain conf_h)). simpl. assumption. apply
  env_eq_fresh. assumption. destruct (fresh (domain conf_h)). assumption.
  exists x. destruct x. split. apply App with (B:=b) (Ψ:=conf_h)
  (ne:= l0).  assumption. simpl. destruct y. assumption.  destruct y.
  assumption.   
Qed. 
