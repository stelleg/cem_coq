Require Import util cesm im db db_assembly assembly relations List cem.
Import ListNotations.

Open Scope nat_scope. 
Variable new : ∀ (n:nat) (h : im.Heap), sigT (λ w:nat, ∀ i, lt i n → (i+w) ∉ domain h).

Definition prog_eq (p : Ptr) (pr : Program) (t : tm) := 
  let subpr := assemble t p in subpr = firstn (length subpr) (skipn p pr).

Inductive env_eq : nat → cem.heap → 
                   Program → Ptr → im.Heap → Type := 
  | ee : ∀ n ch pr p ih e e' c c' ip t, 
    lookup n ch = Some (cl (close t e) c) →
    lookup p ih = Some ip → 
    lookup (1+p) ih = Some e' → 
    lookup (2+p) ih = Some c' → 
    prog_eq ip pr t → 
    env_eq e ch pr e' ih →    
    env_eq c ch pr c' ih →    
    env_eq n ch pr p ih.
  
Inductive clos_eq : cem.closure → cem.heap → 
                    Ptr → Ptr → Program → im.Heap → 
                    Type :=
  | c_eq : ∀ t e ch p ip ep ih, 
           prog_eq ip p t → 
           env_eq e ch p ep ih →
           clos_eq (cem.close t e) ch ip ep p ih.

Inductive stack_eq : cesm.stack → cesm.heap →
                     im.Stack → Program → im.Heap → Type := 
  | stack_nil : ∀ ch p ih, 
                stack_eq nil ch nil p ih
  | stack_upd : ∀ e ch p ep ih cs is, 
                 env_eq e ch p ep ih →
                 stack_eq cs ch is p ih →
                 stack_eq (inr e::cs) ch (0::ep::is) p ih
  | stack_arg : ∀ ch p ip ep ih cs is c, 
                 clos_eq c ch ip ep p ih →
                 stack_eq cs ch is p ih → 
                 stack_eq (inl c::cs) ch (S ip::ep::is) p ih.

Inductive state_rel : cesm.state → im.State → Type := 
  | str : ∀ cs is, 
  clos_eq (st_cl cs) (st_hp cs) (rff (st_rf is) IP) (rff (st_rf is) EP) (st_p is) (st_h is) →
  stack_eq (st_st cs) (st_hp cs) (st_s is) (st_p is) (st_h is) →
  state_rel cs is.

Lemma skipn_nth_error {A} : ∀ y l (x:A) xs, skipn y l = x::xs → nth_error l y = Some x. 
induction y; intros. simpl in H. simpl. destruct l. invert H. invert H. auto.
simpl in H. destruct l. invert H. simpl. apply IHy with (xs:=xs). assumption. 
Qed. 

Lemma skipn_nth_error_1 {A} : ∀ y l (x x':A) xs, skipn y l = x::x'::xs →
nth_error l (1 + y) = Some x'. 
induction y; intros. simpl in H. simpl. destruct l. invert H. invert H. auto.
simpl in H. destruct l. invert H. simpl. apply IHy with (x:=x) (xs:=xs). assumption. 
Qed. 

Lemma skipn_nth_error_2 {A} : ∀ y l (x x1 x2:A) xs, skipn y l = x::x1::x2::xs →
nth_error l (2 + y) = Some x2. 
induction y; intros. simpl in H. simpl. destruct l. invert H. invert H. auto.
simpl in H. destruct l. invert H. simpl. apply IHy with (x:=x) (x1:=x1) (xs:=xs). assumption. 
Qed. 

Lemma fresh_closure : ∀ ip ep e f h, (∀ i, lt i 3 → (i+f) ∉ domain h) → 
  replace beq_nat (2+f) e (replace beq_nat (1+f) ep (replace beq_nat f ip 
    ((f,0)::(S f, 0)::(S (S f), 0)::h))) = (f,ip)::(S f, ep)::(S (S f), e)::h.
intros.  
unfold replace. unfold map. 
unfold plus. 
assert (beq_nat (S (S f)) (S f) = false). clear H. induction f; auto.  
assert (beq_nat (S (S f)) f = false). clear H. induction f; auto.  
assert (beq_nat (S f) f = false). clear H. induction f; auto.  
repeat (rewrite <- beq_nat_refl). 
rewrite H2. rewrite H1. rewrite beq_nat_comm. rewrite H2. rewrite <- beq_nat_refl. 
rewrite H0. rewrite beq_nat_comm. rewrite H1. rewrite beq_nat_comm. rewrite H0.
rewrite <- beq_nat_refl. 
clear H0 H1 H2. 
  assert (f ∉ domain h). apply (H 0); auto. 
  assert (S f ∉ domain h). apply (H 1); auto. 
  assert (S (S f) ∉ domain h). apply (H 2); auto. 
apply replace_not_in with (c:=ip) in H0. 
apply replace_not_in with (c:=ep) in H1.
apply replace_not_in with (c:=e)  in H2. 
unfold replace in *. unfold map in *. 
rewrite H0. rewrite H1. rewrite H2. reflexivity. 
Qed. 

Lemma cesm_im : ∀ v s s', 
  state_rel s s' → 
  cesm.step s v → 
  sigT (λ v', prod (refl_trans_clos im.step s' v') (state_rel v v')).
intros v s s' r h. induce h. 
- invert r. invert X. simpl in *. invert X0. destruct s' as [rf p is' h]. simpl
  in *. subst. exists (st (upd R1 ep rf) p is (replace beq_nat (1 + ep)
  (im.ep rf) (replace beq_nat ep (ip rf) h))). split.  
  + apply t_step with (y:=st (upd IP (1 + ip rf) (upd R1 0 rf)) p (ep::is)
    h). invert H6.  destruct (skipn (ip rf) p) eqn:snip. invert H0. apply enter
    with (k:=ip rf) (bb:=b0).  constructor. apply skipn_nth_error in snip.
    assumption. invert H0.  eapply step_pop. constructor.  eapply step_jump0.
    destruct rf. simpl.  constructor.  constructor.  simpl.  apply t_step with
    (y:=st (upd R1 ep rf) p is (replace beq_nat (1 + ep) (im.ep rf) (replace
    beq_nat ep (ip rf) h))).  invert H6.  destruct (skipn (ip rf) p)
    eqn:skip. inversion H0.  destruct l0 eqn:l0e.  invert H0.  subst. apply
    skipn_nth_error_1 in skip.  apply enter with (k:=1 + ip rf) (bb:=b1).
    destruct rf. constructor.  assumption.  inversion H0.  subst.  eapply
    step_pop.  constructor. eapply step_mov.  constructor. eapply write_mem.
    eapply step_mov.  constructor.  eapply write_mem. eapply step_jump.
    constructor.  simpl. destruct rf. simpl in *. eapply write_reg. apply
    t_refl. 
  + admit. 
- generalize dependent e0. generalize dependent r. generalize dependent e.
  generalize dependent l. generalize dependent e'. generalize dependent s'.
  generalize dependent c. induction v; intros. 
  * invert r. invert X. destruct s'. simpl in *. invert H6. destruct (skipn (ip
  st_rf) st_p) eqn:skip. invert H0. invert H0. apply skipn_nth_error in skip.
  simpl in *. destruct (lookup e Φ) eqn:luΦ. Focus 2. invert e0. destruct c0. invert e0. invert X1.
  rewrite luΦ in H.  invert H. destruct st_rf; simpl in *. exists (st (mkrf ip
  e'0 ip r2) st_p (0::ep::st_s) st_h). split. 
    + eapply t_step. eapply enter.
      constructor. apply skip. eapply step_push. constructor. eapply step_push.
      constructor. eapply step_mov. constructor. simpl. apply H0.  constructor.
      eapply step_mov. constructor. simpl. apply H1. constructor.  eapply
      step_jump. constructor. constructor. simpl. eapply t_refl.  
    + admit. 
  * simpl in e0. destruct (lookup e Φ) eqn:lue. destruct c0. eapply (IHv _ _ _ _
    _ _ e0). invert e0.  
- destruct s'. invert r. simpl in *. invert X. invert X0. destruct st_rf. simpl
  in *. destruct (new 3 st_h) as [f' ff']. exists (st (mkrf (3+ip0) f (S ip) f')
  st_p is ((f',ip)::(1+f',ep)::(2+f',ep0)::st_h)). split. 
  + eapply t_step. eapply enter; simpl. constructor. simpl. invert H6. destruct
  (skipn ip0 st_p) eqn:skip. invert H0. invert H0. apply skipn_nth_error in
  skip. apply skip. eapply step_pop. constructor. eapply step_jumpS.
  simpl. eapply (read_reg R1 (st (mkrf ip0 ep0 (S ip) r2) st_p (ep::is) st_h)). 
  constructor. constructor. simpl. eapply t_step. eapply enter. constructor. 
  simpl. invert H6. destruct (skipn ip0 st_p) eqn:skip. invert H0. destruct l.
  invert H0. destruct l. invert H0. invert H0. apply skipn_nth_error_2 in skip.
  apply skip. eapply step_new. apply ff'. repeat (econstructor). eapply step_mov.
  constructor. constructor. repeat (econstructor). unfold rff. unfold im.r2.
  unfold upd. unfold im.ep. unfold st_rf. unfold im.r1. rewrite plus_O_n. unfold
  zeroes. unfold app. rewrite fresh_closure. apply t_refl.  rewrite simpl.  rewrite
  PeanoNat.Nat.eqb_refl. assert (PeanoNat.Nat.eqb f' (S (S f')) = false). clear ff'. 
  induction f'; auto. rewrite H. simpl. apply IHf'. assumption. rewrite PeanoNat.Nat.add_comm. simpl.   
  apply r. . 
  so



specialize (IHv _ _
  * _ _ _ _ lue). invert r. invert X.
  * jump0.  with
  (y:=(st (mkrf ip e'0 ip r2) st_p (0::ep::st_s) st_h)). eapply apply 
  destruct rf. simpl in *. constructor; simpl. constructor. assumption. clear
  H6. clear X2. induce X1. constructor; simpl. constructor.
    assumption. destruct (eq_nat_dec n l). subst. eapply ee. apply lookup_update with
    (c:=close t e). apply e0. apply lookup_update'. apply e0. in e0. . eapply
    IHX1_2. constructor; simpl. constructor.
    eapply IHX1_2. assumption.  eapply ee. invert X1.  
- 
  constructor.  destruct invert
  H6. invert H0.  apply enter with (k:=.  apply match r with r
Admitted.

Lemma cesm_im_assemble : ∀ t v v', 
  refl_trans_clos cesm.step (cesm.I t) v → 
  refl_trans_clos im.step (im.I (assemble t 1)) v'.
Admitted.

