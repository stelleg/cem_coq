Require Import util cesm im db db_assembly assembly relations List cem.
Import ListNotations.
Require Import Program.

Open Scope nat_scope. 
(*
Variable new : ∀ (n:nat) (h : im.Heap), sigT (λ w:nat, 
  prod (∀ i, lt i n → (i+w) ∉ domain h)
       (w > 0)).
*)

Definition prog_eq (p : Ptr) (pr : Program) (t : tm) := 
  let subpr := assemble t p in subpr = firstn (length subpr) (skipn p pr).

(*
Inductive env_eq : nat → cem.heap → 
                   Program → Ptr → im.Heap → Type := 
  | ee : ∀ n ch pr p ih e e' c c' ip t, 
    (lookup n ch = Some (cl (close t e) c) →
    (prod (lookup p ih = Some ip)  
    (prod (lookup (1+p) ih = Some e')
    (lookup (2+p) ih = Some c')))) → 
    prog_eq ip pr t → 
    env_eq e ch pr e' ih →    
    env_eq c ch pr c' ih →    
    env_eq n ch pr p ih.
*)  
(*
Inductive heap_eq : (nat, cell) → (Ptr * Ptr * Ptr * Ptr), P → cem.heap → im.heap → Type :=
  | heap_eq_tail : ∀ l p, (l, 
*)

Inductive heap_rel : cesm.heap → im.Heap → Type := 
  | heap_nil : heap_rel [] [] 
  | heap_cons : ∀ l l' ne ch ih ip ep ine e t, 
    l ∉ domain ch → l' ∉ domain ih → S l' ∉ domain ih → S (S l') ∉ domain ih →
    l > 0 → l' > 0 → 
    heap_rel ch ih → 
    heap_rel 
      ((l, cl (close t e) ne)::ch) 
      ((l', ip)::(S l', ep)::(S (S l'), ine)::ih).

(*
Inductive in_heap : ∀ (ch : cesm.heap) (ih : im.Heap) (r : heap_rel ch ih) 
  (l e ne : nat) (t : db.tm) (il ip ep nep : Ptr), Type :=
  | in_heap_head : in_heap_rel ((l, cl (close t e) ne)::ch)
                               ((il, ip)::(S il, ep)::(S (S il), ine)::ih)
  | in_heap_tail : in_heap_rel ch ih r l e ne t il ip ep nep →
                   in_heap_rel ((l', cl (close t' e') ne')::ch) 
                               ((il', ip)::(S il', ep)::(S (S il'), ine)::ih)
                               (heap_cons 
*)
  
  
Open Scope type_scope.
Fixpoint in_heap_rel (ch : cesm.heap) (ih : im.Heap)
                     (r : heap_rel ch ih)
                     (l e ne : nat) (t : db.tm) 
                     (il ip ep nep : Ptr) : Type := match r with
  | heap_nil => False
  | heap_cons l' il' ne' cht iht ip' ep' nep' e' t' _ _ _ _ _ _ rt => 
    if andb (beq_nat l l') (beq_nat il il') then
    (ne' = ne) *  (ip' = ip) * (ep' = ep) * (nep' = nep) * (e' = e) * (t' = t)
    else 
      if andb (negb (beq_nat l l')) (negb (beq_nat il il'))
        then in_heap_rel cht iht rt l e ne t il ip ep nep
        else False
  end.

Inductive env_eq (ch : cesm.heap) (ih : im.Heap) (r : heap_rel ch ih) (p : Program)
  : nat → Ptr → Type :=
  | e0 : env_eq ch ih r p 0 0 
  | eS : ∀ l e ne t il ip ep nep, 
    in_heap_rel ch ih r l e ne t il ip ep nep →
    env_eq ch ih r p l il.

Inductive heap_eq (ch : cesm.heap) (ih : im.Heap) (r : heap_rel ch ih) (p : Program) : Type:=
  | mkheap_eq : 
    (∀ l e ne t il ip ep nep, 
      in_heap_rel ch ih r l e ne t il ip ep nep →
      (prog_eq ip p t) * 
      (env_eq ch ih r p e ep) * 
      (env_eq ch ih r p ne nep)) → 
    heap_eq ch ih r p.

(*
Open Scope type_scope.
Definition zipped := list ((nat * Ptr) * (cell * Ptr * Ptr * Ptr)).
Fixpoint zipHeaps (ch : cesm.heap) (ih : im.Heap) : zipped := match ch, ih with
    | (l,c)::ch, (l0,ip)::(l1,ep)::(l2,ine)::ih => 
        if andb (beq_nat l1 (1+l0)) (beq_nat l2 (2+l0)) then
        ((l, l0), (c, ip, ep, ine))::zipHeaps ch ih
        else nil
    | _, _ => nil
    end.

Fixpoint lookupZip (key: (nat * Ptr)) (z: zipped)  : 
  option (cell * Ptr * Ptr * Ptr) := match z,key with
  | nil, _ => None
  | ((x,y),v)::xs, (x',y') => if andb (beq_nat x x') (beq_nat y y') then Some v else
    lookupZip key xs
  end.

Lemma luz_lu : ∀ ch ih l l' c i e n, 
  lookupZip (l, l') (zipHeaps ch ih) = Some (c, i, e ,n) →
  lookup l ch = Some c →
  lookup l ih = Some i →
  lookup (1+l) ih = Some e →
  lookup (1+l) ih = Some n.
induction ch; intros. inversion H. destruct a. simpl in H. destruct ih.
inversion H. destruct p. destruct ih. invert H. destruct p0. destruct ih. invert
H. destruct p1. destruct (PeanoNat.Nat.eqb p0 (S p)) eqn:p0sp.  destruct
(PeanoNat.Nat.eqb p1 (S (S p))). zipHeaps ch ih) eqn:zh. inversion H. destruct a. destruct p. 
simpl in H. destruct p0. unfolddestruct 
*)

Lemma in_heap_rel_lookup : ∀ ch ih r l e ne t il ip ep nep, 
  in_heap_rel ch ih r l e ne t il ip ep nep →
  (lookup l ch = Some (cl (close t e) ne)) *
  (lookup il ih = Some ip) *
  (lookup (1+il) ih = Some ep) *
  (lookup (2+il) ih = Some nep).
intros. induce r. invert X. 
simpl in X. destruct (eq_nat_dec l0 l). destruct (eq_nat_dec il l'). subst. 
repeat (rewrite <- beq_nat_refl in X). simpl in X. repeat (destruct X as [X]).
subst. rewrite lookup_head. rewrite lookup_head. rewrite lookup_head'; auto. 
rewrite lookup_head. rewrite lookup_head'. rewrite lookup_head'. rewrite
lookup_head. crush. crush. crush. subst. rewrite <- beq_nat_refl in X. 
rewrite <- PeanoNat.Nat.eqb_neq in n3. repeat (rewrite n3 in X). simpl in X.
invert X. destruct (eq_nat_dec il l'). subst. rewrite <- PeanoNat.Nat.eqb_neq in
n3. rewrite n3 in X. rewrite <- beq_nat_refl in X. simpl in X. invert X. 
rewrite <- PeanoNat.Nat.eqb_neq in n3.  rewrite <- PeanoNat.Nat.eqb_neq in n4.
rewrite n3 in X. rewrite n4 in X. simpl in X. apply IHr in X. inversion X.
invert H. invert H1.  
apply lookup_domain in H0. apply lookup_domain in H2. apply lookup_domain in H.
apply lookup_domain in H3. 
pose (in_notin_neq _ _ _ H0 n0). 
pose (in_notin_neq _ _ _ H0 n1). 
pose (in_notin_neq _ _ _ H0 n2). 
pose (in_notin_neq _ _ _ H2 n0). 
pose (in_notin_neq _ _ _ H2 n1).
pose (in_notin_neq _ _ _ H2 n2). 
pose (in_notin_neq _ _ _ H3 n0). 
pose (in_notin_neq _ _ _ H3 n1). 
pose (in_notin_neq _ _ _ H3 n2). 
pose (in_notin_neq _ _ _ H n). 
repeat (rewrite lookup_head'; auto). 
Qed.

(*
Open Scope type_scope. 
Lemma heap_rel_lookup : ∀ l l' ne ch ih ip ep ine e t, 
  heap_rel l e ne t l' ip ep ine ch ih → 
  (lookup l ch = Some (cl (close t e) ne)) *
  (lookup l' ih = Some ip) * 
  (lookup (1+l') ih = Some ep) *
  (lookup (2+l') ih = Some ine).
intros. induce X. 
split. split. split. apply lookup_head. apply lookup_head. rewrite lookup_head';
auto. apply lookup_head. rewrite lookup_head'; auto. rewrite lookup_head'. apply
lookup_head. simpl. auto. induction l'; auto. simpl. auto. destruct IHX.
destruct p. destruct p. split. split. split.  rewrite lookup_head'; auto.
rewrite lookup_head'; auto. rewrite lookup_head'; auto.  rewrite lookup_head';
auto. simpl. rewrite lookup_head'; auto. rewrite lookup_head'; auto. rewrite
lookup_head'; auto. repeat (rewrite lookup_head'; auto). simpl. crush. crush.
Qed.  

Inductive env_eq' : nat → cesm.heap → Program → Ptr → im.Heap → Type :=
  | e0 : ∀ h ih p, env_eq' 0 h p 0 ih
  | en : ∀ l e ne t il ip ie ine h ih p,
    heap_rel l e ne t il ip ie ine h ih →  
    prog_eq ip p t →
    env_eq' e h p ie ih →
    env_eq' ne h p ine ih →
    env_eq' l h p il ih.
*)   

Inductive clos_eq (ch : cem.heap) (ih : im.Heap) (r : heap_rel ch ih) (p : Program):
                  closure → Ptr → Ptr → Type :=
  | c_eq : ∀ t e ip ep, 
           prog_eq ip p t → 
           env_eq ch ih r p e ep →
           clos_eq ch ih r p (cem.close t e) ip ep. 

Inductive stack_eq (ch : cem.heap) (ih : im.Heap) (r : heap_rel ch ih) (p : Program) : 
  cesm.stack → im.Stack → Type := 
  | stack_nil : stack_eq ch ih r p nil nil
  | stack_upd : ∀ l e ne t il ip ie ine cs is, 
                in_heap_rel ch ih r l e ne t il ip ie ine →
                stack_eq ch ih r p cs is →
                stack_eq ch ih r p (inr l::cs) (0::il::is)
  | stack_arg : ∀ ip ep cs is c, 
                 ip > 0 →
                 clos_eq ch ih r p c ip ep →
                 stack_eq ch ih r p cs is → 
                 stack_eq ch ih r p (inl c::cs) (ip::ep::is).

Inductive state_rel (cs : cesm.state) (is : im.State) : Type := 
  | str : ∀ r, 
  heap_eq (st_hp cs) (st_h is) r (st_p is) →
  clos_eq (st_hp cs) (st_h is) r (st_p is) (st_cl cs) (rff (st_rf is) IP) (rff (st_rf is) EP) →
  stack_eq (st_hp cs) (st_h is) r (st_p is) (st_st cs) (st_s is) →
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

Lemma firstn_pref {a}: ∀ x y:list a, x = firstn (length x) y → ∃ z, y = x ++ z. 
induction x; intros. exists y. auto. 
simpl in H. destruct y. invert H. invert H. rewrite <- H2. apply IHx in H2.
destruct H2. exists x0. simpl. subst. f_equal. 
Qed.   

Lemma firstn_app_length {a} : ∀ (x y:list a) p, x ++ y = firstn (length (x ++ y)) p → 
  x = firstn (length x) p ∧ y = firstn (length y) (skipn (length x) p). 
intros. apply firstn_pref in H. destruct H. subst. rewrite <- app_assoc.
generalize dependent y. generalize dependent x0. induction x; intros. simpl.
split; auto. induction y. simpl. reflexivity. simpl. rewrite <- IHy.
reflexivity. simpl. split. f_equal. destruct (IHx x0 y). assumption. destruct
(IHx x0 y). assumption. Qed. 

Lemma skipn_cons {a} : ∀ xs (x:a) n, skipn (S n) (x::xs) = skipn n xs. 
induction xs; intros. simpl. reflexivity. simpl. reflexivity. 
Qed.  

Lemma skipn_cons' {a} : ∀ n xs (x:a) ys, skipn n ys = (x::xs) → skipn (S n) ys = xs.
induction n; intros. simpl. simpl in H. subst. reflexivity. destruct ys. simpl
in H. invert H. simpl in H. apply IHn in H. rewrite skipn_cons. assumption.  
Qed.  

Lemma skipn_nil {a} : ∀ n, skipn n (@nil a) = (@nil a). 
intros. destruct n; auto. Qed. 

Lemma skipnm_add {a} : ∀ m n (xs:list a), skipn n (skipn m xs) = skipn (n + m) xs.
induction m; intros. simpl. rewrite <- plus_n_O. reflexivity. rewrite
PeanoNat.Nat.add_comm. simpl. destruct xs. apply skipn_nil. rewrite
PeanoNat.Nat.add_comm. apply IHm. Qed. 

Open Scope nat_scope. 
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

Lemma lu_update_none : ∀ Φ l l' v, lookup l Φ = None → lookup l (update Φ l' v) = None.
induction Φ; intros. simpl. unfold lookup. unfold find. reflexivity.
destruct a. destruct c. destruct (eq_nat_dec l' n). subst. simpl. rewrite
<- beq_nat_refl. destruct (eq_nat_dec l n). subst. rewrite lookup_head in H.
invert H. rewrite lookup_head' in H; auto. rewrite lookup_head'; auto. unfold
update. rewrite <- PeanoNat.Nat.eqb_neq in n0. rewrite n0. destruct (eq_nat_dec
l n). subst. rewrite lookup_head in H. invert H. rewrite lookup_head'; auto.
apply IHΦ. rewrite lookup_head' in H; auto. 
Qed. 

Lemma lu_replace_none {a} : ∀ h l l' (v:a), lookup l h = None → 
  lookup l (replace beq_nat l' v h) = None.
induction h; intros. simpl. unfold lookup. unfold find. reflexivity.
destruct a0. destruct (eq_nat_dec l' n). subst. simpl. rewrite
<- beq_nat_refl. destruct (eq_nat_dec l n). subst. rewrite lookup_head in H.
invert H. rewrite lookup_head' in H; auto. rewrite lookup_head'; auto. unfold
update. rewrite <- PeanoNat.Nat.eqb_neq in n0. unfold replace. simpl. rewrite
n0. destruct (eq_nat_dec l n). subst. rewrite lookup_head in H. invert H.
rewrite lookup_head'; auto. unfold replace in IHh. apply IHh. rewrite
lookup_head' in H; auto.  Qed. 

Lemma update_head : ∀ l c ne h v, update (l ↦ cl c ne::h) l v = 
                                  l ↦ cl v ne::update h l v. 
intros. unfold update. rewrite <- beq_nat_refl. reflexivity. 
Qed. 

Lemma update_head' : ∀ l c ne h v l', 
  l <> l' →
  update (l' ↦ cl c ne::h) l v = 
  l' ↦ cl c ne::update h l v. 
intros. unfold update. rewrite <- PeanoNat.Nat.eqb_neq in H. rewrite H. reflexivity. 
Qed. 

Lemma replace_head {a} : ∀ l (y x:a) h, replace beq_nat l x ((l,y)::h) = 
                                        (l,x)::replace beq_nat l x h.
intros. unfold replace. simpl. rewrite <- beq_nat_refl. reflexivity. Qed. 

Lemma replace_head' {a} : ∀ l (y x:a) h l',  l <> l' →
  replace beq_nat l x ((l',y)::h) = 
  (l',y)::replace beq_nat l x h.
intros. unfold replace. simpl. rewrite <- PeanoNat.Nat.eqb_neq in H. rewrite H. 
reflexivity. Qed. 

Lemma update_head_exists : ∀ l l' c ne v h, sigT (λ c', update ((l', cl c ne)::h) l v =
  (l', cl c' ne)::update h l v).
intros. simpl. destruct (beq_nat l l'). exists v; auto. exists c; auto. Qed.

Lemma replace_head_exists {a} : ∀ l l' (x:a) h v, sigT (λ y, replace beq_nat l v ((l', x)::h) =
  (l', y)::replace beq_nat l v h).
intros. simpl. destruct (beq_nat l l'). exists v; auto. exists x; auto. Qed.

Lemma in_heap_cons : ∀ prop ch ih r l' e' ne' t' il' ip' ep' nep', 
  (∀ l e ne t il ip ep nep, 
    in_heap_rel ch ih r l e ne t il ip ep nep → 
    prop l e ne t il ip ep nep) → 
  ∀ pl pil pil1 pil2 plg pilg,
  prop l' e' ne' t' il' ip' ep' nep' →
  (∀ l e ne t il ip ep nep, 
    in_heap_rel ((l', cl (close t' e') ne')::ch) 
                ((il', ip')::(S il',ep')::(S (S il'),nep')::ih) 
                (heap_cons _ _ _ _ _ _ _ _ _ _ pl pil pil1 pil2 plg pilg r) 
                l e ne t il ip ep nep →
    prop l e ne t il ip ep nep).
intros. simpl in X1. destruct (beq_nat l l') eqn:ll'. destruct (beq_nat il il')
eqn:ilil'. simpl in X1. repeat (destruct X1 as [X1]). apply beq_nat_true in ll'.
apply beq_nat_true in ilil'. subst. assumption. simpl in X1. invert X1. destruct
(beq_nat il il') eqn:ilil'. simpl in X1. invert X1. simpl in X1. apply X in X1.
assumption. Qed.

Lemma in_heap_head : ∀ l l' ne ch ih ip ep ine e t f0 f1 f2 f3 f4 f5 r, 
  in_heap_rel ((l, cl (close t e) ne)::ch) 
              ((l', ip)::(S l', ep)::(S (S l'), ine)::ih)    
    (heap_cons l l' ne ch ih ip ep ine e t f0 f1 f2 f3 f4 f5 r)
    l e ne t l' ip ep ine.
intros. simpl. rewrite <- beq_nat_refl. rewrite <- beq_nat_refl. simpl. crush. 
Qed. 
    
Lemma in_heap_rel_upd_head : 
  ∀ l l' il il' t t' e e' ne ne' ip ep nep ip' ep' nep' ch ih r pl pil psil
  pssil gl gil, 
  in_heap_rel ((l, cl (close t e) ne)::ch) 
              ((il, ip)::(S il, ep)::(S (S il), nep)::ih)
              (heap_cons l il ne ch ih ip ep nep e t pl pil psil pssil gl gil r)
              l' e' ne' t' il' ip' ep' nep' → 
  (l = l') * (ne = ne') * (il = il') * (nep = nep') * (t = t') * (e = e') * (ip = ip') * (ep = ep') + 
  (l ≠ l') * (il ≠ il') * (S il ≠ il') * (S (S il) ≠ il') * in_heap_rel ch ih r l' e' ne' t' il' ip' ep' nep'. 
intros. simpl in X.  destruct (eq_nat_dec l l'); destruct (eq_nat_dec il il').
subst. rewrite <- beq_nat_refl in X. rewrite <- beq_nat_refl in X. simpl in X.
crush. rewrite <- PeanoNat.Nat.eqb_neq in n. rewrite beq_nat_comm in n. rewrite
n in X.  simpl in X. subst. rewrite <- beq_nat_refl in X.  simpl in X. invert X.
subst. rewrite <- PeanoNat.Nat.eqb_neq in n. rewrite beq_nat_comm in n. rewrite
n in X. simpl in X. rewrite <- beq_nat_refl in X. simpl in X. invert X. apply
inr. apply prod_assoc'. apply prod_assoc'. split. crush. rewrite <-
PeanoNat.Nat.eqb_neq in n. rewrite <- PeanoNat.Nat.eqb_neq in n0.  rewrite
beq_nat_comm in n. rewrite beq_nat_comm in n0. rewrite n in X.  rewrite n0 in X.
simpl in X. apply prod_assoc.  split. apply in_heap_rel_lookup in X. destruct X. destruct p.
destruct p. apply lookup_domain in e4. split. unfold not. intros. subst. apply
psil in e4. invert e4. unfold not. intros. subst. apply pssil in e4. invert e4.
assumption. Qed.  

Lemma in_heap_rel_upd_head' :
  ∀ l l' il il' t t' e e' ne ne' ip ep nep ip' ep' nep' ch ih r pl pil psil
  pssil gl gil, 
  (l = l') * (ne = ne') * (il = il') * (nep = nep') * (t = t') * (e = e') * (ip = ip') * (ep = ep') + 
  (l ≠ l') * (il ≠ il') * in_heap_rel ch ih r l' e' ne' t' il' ip' ep' nep' →
  in_heap_rel ((l, cl (close t e) ne)::ch) 
              ((il, ip)::(S il, ep)::(S (S il), nep)::ih)
              (heap_cons l il ne ch ih ip ep nep e t pl pil psil pssil gl gil r)
              l' e' ne' t' il' ip' ep' nep'. 
intros. destruct X. crush. rewrite <- beq_nat_refl. rewrite <- beq_nat_refl.
simpl. crush. destruct p. simpl. destruct p. rewrite <- PeanoNat.Nat.eqb_neq in
n. rewrite <- PeanoNat.Nat.eqb_neq in n0. rewrite beq_nat_comm. rewrite n.
rewrite beq_nat_comm. rewrite n0. simpl. assumption. Qed.

Lemma forall_heap_rel_tail : ∀ l il t e ne ip ep nep ch ih
  r pl pil psil pssil gl gil prop, 
  (∀ l' e' ne' t' il' ip' ep' nep', in_heap_rel 
    ((l, cl (close t e) ne)::ch) 
    ((il, ip)::(S il, ep)::(S (S il), nep)::ih) 
    (heap_cons l il ne ch ih ip ep nep e t pl pil psil pssil gl gil r) 
    l' e' ne' t' il' ip' ep' nep' →
    prop t' e' ip' ep') → 
  (∀ l' e' ne' t' il' ip' ep' nep', in_heap_rel 
    ch 
    ih 
    r 
    l' e' ne' t' il' ip' ep' nep' →
    prop t' e' ip' ep'). 
intros. apply X with (l':=l') (ne':=ne') (il':=il') (nep':=nep'). apply
in_heap_rel_upd_head'. apply inr. split; auto. apply in_heap_rel_lookup
in X0. destruct X0. destruct p. destruct p. apply lookup_domain in e3. apply
lookup_domain in e4. split; (unfold not; intros; subst). 
apply pl in e3. assumption. apply pil in e4. assumption. 
Qed. 

Lemma contractable_heap_rel : ∀ ch ih (r1 r2: heap_rel ch ih), r1 = r2.  
intros. induce r1. dependent destruction r2. reflexivity. dependent destruction
r2. 
rewrite (proof_irrelevance _ n n3). 
rewrite (proof_irrelevance _ n0 n4). 
rewrite (proof_irrelevance _ n1 n5). 
rewrite (proof_irrelevance _ n2 n6). 
rewrite (proof_irrelevance _ g g1). 
rewrite (proof_irrelevance _ g0 g2). 
rewrite (IHr1 r2). reflexivity. 
Qed. 

Lemma in_heap_rel_upd : ∀ ch ih r l e ne t il ip ep nep ep' ip' v e' 
  (prop : tm → nat → Ptr → Ptr → Type),
  (∀ l e ne t il ip ep nep, in_heap_rel ch ih r l e ne t il ip ep nep → 
                            prop t e ip ep) →
  in_heap_rel ch ih r l e ne t il ip ep nep →
  prop v e' ip' ep' →
  sigT (λ r', (∀ l' e ne t il' ip ep nep, 
      (in_heap_rel (update ch l (close v e')) 
                  (replace beq_nat (S il) ep' (replace beq_nat il ip' ih)) 
                  r' l' e ne t il' ip ep nep) → prop t e ip ep)).
intros. induce r. invert X0. assert (X0' := X0). apply in_heap_rel_upd_head in
X0'. destruct X0'. 
- repeat (destruct p). subst. rewrite update_head. rewrite replace_head. rewrite
  replace_head'; auto.  rewrite replace_head'; auto. rewrite replace_head.
  rewrite replace_head'.  rewrite replace_head'.  rewrite replace_not_in.
  rewrite replace_not_in. rewrite update_nodomain; auto. 
  exists (heap_cons l0 il ne0 ch ih ip' ep' nep e' v n n0 n1 n2 g g0 r).
  intros. apply in_heap_rel_upd_head in X2. destruct X2. repeat
  destruct p. subst. assumption. apply (X l' _ ne _ il' _ _ nep0). apply
  in_heap_rel_upd_head'. apply inr. crush. auto. rewrite replace_not_in.
  assumption. assumption. auto. crush.   
- assert (n' := n). 
  assert (n0' := n0). 
  assert (n1' := n1).
  assert (n2' := n2). 
  rewrite <- domain_update with (l:=l0) (v:=close v e') in n'. 
  rewrite replace_domain with (l1:=il) (eq0:=beq_nat) (v0:=ip') in n0'. 
  rewrite replace_domain with (l1:=S il) (eq0:=beq_nat) (v0:=ep') in n0'.
  rewrite replace_domain with (l1:=il) (eq0:=beq_nat) (v0:=ip') in n1'. 
  rewrite replace_domain with (l1:=S il) (eq0:=beq_nat) (v0:=ep') in n1'.
  rewrite replace_domain with (l1:=il) (eq0:=beq_nat) (v0:=ip') in n2'. 
  rewrite replace_domain with (l1:=S il) (eq0:=beq_nat) (v0:=ep') in n2'.
  specialize (IHr l0 e1 ne0 t0 il ip0 ep0 nep ep' ip' v e' prop).
  destruct p. repeat (destruct p).  
  rewrite update_head'. Focus 2. crush. 
  repeat (rewrite replace_head'; auto). Focus 2. apply in_heap_rel_lookup in i.
  destruct i. repeat (destruct p). simpl in e3. apply lookup_domain in e3. apply
  (in_notin_neq (S il) l' (domain ih)); auto.  
  assert (ihr := forall_heap_rel_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X). 
  specialize (IHr ihr i X1). destruct IHr. 
  exists (heap_cons l l' ne 
         (update ch l0 (close v e')) 
         (replace beq_nat (S il) ep' (replace beq_nat il ip' ih))
         ip ep ine e t n' n0' n1' n2' g g0 x).
  intros. 
  apply in_heap_rel_upd_head in X2. destruct X2.   
  repeat (destruct p0). subst. assert (ihh := in_heap_head). apply X in ihh.
  assumption. repeat (destruct p0). (*rewrite (contractable_heap_rel _ _ r' x) in
  i0.*) apply p in i0. assumption. 
  Qed. 

Lemma in_heap_rel_upd : ∀ ch ih r l e ne t il ip ep nep ep' ip' v p e', 
  in_heap_rel ch ih r l e ne t il ip ep nep →
  heap_eq ch ih r p → 
  prog_eq ip' p v →
  env_eq ch ih r p e' ep' → 
  sigT (λ r', heap_eq (update ch l (close v e'))
          (replace beq_nat (S il) ep' (replace beq_nat il ip' ih))
          r'
          p).
intros. induce r. 
- simpl. exists heap_nil. constructor. simpl. intros. invert H0.      
- invert X0. apply in_heap_rel_upd_head in X. destruct X. 
  + repeat (destruct p0).     exists (heap_cons l0 il ne0 ch ih ip' ep' nep e' v n n0 n1 n2 g g0 r).
    specialize (X2 _ _ _ _ _ _ _ _ (in_heap_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _)).  constructor. intros. apply in_heap_rel_upd_head in X. destruct X.
    crush. eapply (eS _ _ _ p e1 e ne t il0 ip ep nep0 _) .  crush. specialize
    (X2 l e1 ne t0 il0 ip0 ep0 nep0).
    rewrite <- beq_nat_refl in X2. rewrite <- beq_nat_refl in X2. simpl in X2.
    crush. const assumption. split. split.  h
    assumption. 
    rewrite
  replace_head. simpl. rewrite <- beq_nat_refl. rewrite <-
  beq_nat_refl. destruct il. crush p0. pply X2 in X. destruct X. destruct p0. apply in_heap_rel_upd_head
  in X2. simpl. simpl in 
  destruct (beq_nat l0 l) eqn:l0l.             
  destruct (beq_nat il l') eqn:ill'. simpl in X. apply beq_nat_true in l0l. apply
beq_nat_true in ill'. subst. repeat (destruct X as [X]). subst. 
rewrite update_head. rewrite replace_head. rewrite
replace_head'; auto. rewrite replace_head'; auto. rewrite replace_head. rewrite
replace_head'; auto. rewrite replace_head'; auto. 
rewrite update_nodomain; auto. repeat (rewrite replace_not_in); auto. 
eapply (existT _ (heap_cons l l' ne ch ih ip' ep' ine e' v n n0 n1 n2 r)).
constructor. apply in_heap_cons.    
constructor. intros. simpl in X0. destruct (beq_nat l0 l) eqn:l0l. destruct
(beq_nat il l') eqn:ill'. simpl in X0. crush.   
subst. pose r. eapply heap_cons in h; auto. exists
h. constructor. intros. destruct X0. simpl in p0. inversion h. subst. unfold
in_heap_rel in X. simpl in X. destruct X0. assumption.  assert (ch = update ch l
(close v e')). symmetry. apply update_nodomain.  assumption. rewrite H0 in h.
assert (replace beq_nat (S l') ep' (replace 
destruct X0. eapply heap_cons;
auto. rewrite domain_update. assumption. rewrite <- replace_domain. rewrite
<- replace_domain. assumption. rewrite <- replace_domain. rewrite <-
replace_domain. assumption. repeat (rewrite <- replace_domain). assumption. 
rewrite update_nodomain; auto. repeat (rewrite replace_not_in; auto). crush.
simpl in X. invert X. destruct (PeanoNat.Nat.eqb il l') eqn:ill'. simpl in X. invert X. 
simpl in X. apply beq_nat_false in l0l. apply beq_nat_false in ill'. rewrite
update_head'; auto. specialize (IHr _ _ _ _ _ _ _ _ ep' ip' v X). 
apply in_heap_rel_lookup in X. destruct X. destruct p. destruct p. apply
lookup_domain in e4. apply lookup_domain in e5. apply lookup_domain in e3. apply
lookup_domain in e2.  
pose (in_notin_neq _ _ _ e4 n). 
pose (in_notin_neq _ _ _ e5 n0). 
pose (in_notin_neq _ _ _ e5 n1). 
pose (in_notin_neq _ _ _ e5 n2). 
pose (in_notin_neq _ _ _ e2 n0). 
pose (in_notin_neq _ _ _ e2 n1).
pose (in_notin_neq _ _ _ e2 n2). 
pose (in_notin_neq _ _ _ e3 n0). 
pose (in_notin_neq _ _ _ e3 n1). 
pose (in_notin_neq _ _ _ e3 n2). 
repeat (rewrite replace_head'; auto). apply heap_cons;
auto.  rewrite domain_update. assumption. repeat (rewrite <- replace_domain).
assumption. repeat (rewrite <- replace_domain). assumption. repeat (rewrite <-
replace_domain). assumption.
Qed.

Lemma heap_eq_update' : ∀ ch ih r l e ne t il ip ep nep ep' ip' v p e'
  (ihr : in_heap_rel ch ih r l e ne t il ip ep nep),
  heap_eq ch ih r p → 
  prog_eq ip' p v →
  env_eq ch ih r p e' ep' →
  heap_eq (update ch l (close v e'))
          (replace beq_nat (S il) ep' (replace beq_nat il ip' ih))
          (in_heap_rel_upd ch ih r l e ne t il ip ep nep ep' ip' (close v e') ihr)
          p.
intros. induce r. invert ihr. invert X. simpl. unfold in_heap_rel_up. simpl in X1.split. split. split.  simpl
in ihr. simpl. 


Lemma heap_rel_update' : ∀ l e ne t il ip ie ine Φ ih l' il' ep' ip' v,
  l <> l' → il <> il' → S il <> il' → S (S il) <> il' → il <> S il' → il <> S (S
  il') →
  heap_rel l e ne t il ip ie ine Φ ih →
  heap_rel l e ne t il ip ie ine (update Φ l' v) (replace beq_nat (S il') ep'
  (replace beq_nat il' ip' ih)).
intros. induce X. rewrite update_head'; auto. repeat (rewrite replace_head');
auto. constructor.  
+ subst. destruct c'. edestruct update_head_exists. rewrite e1. 
edestruct (@replace_head_exists nat). rewrite e2. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2. clear e2. 
constructor; auto. 
Qed.
  
Open Scope type_scope. 
Lemma heap_rel_update : ∀ l e ne t il ip ie ine Φ ih
                          l' e' ne' t' il' ip' ie' ine'
                          t'' e'' ie'' ip'',
  heap_rel l e ne t il ip ie ine Φ ih →  
  heap_rel l' e' ne' t' il' ip' ie' ine' Φ ih →
  ∃ ne, heap_rel l' e'' ne' t'' il' ip'' ie'' ine'
        (update Φ l (close t'' e'')) 
        (replace beq_nat (S il) ie''
        (replace beq_nat il ip'' ih))) 
                      +
  ((l <> l') * (il <> il') * heap_rel l' e' ne' t' il' ip' ie' ine'
        (update Φ l (close t'' e''))
        (replace beq_nat (S il) ie''
        (replace beq_nat il ip'' ih))).
intros. induce X. induce X0. invert H1. invert H0. apply inl. split; auto.
rewrite update_head. rewrite replace_head. rewrite replace_head'; auto. rewrite
replace_head'; auto. rewrite replace_head. rewrite replace_head'. rewrite
replace_head'; auto. constructor. crush. invert H1. invert H0. apply inr. split;
auto. rewrite update_head. rewrite replace_head. rewrite replace_head'; auto.
rewrite replace_head'; auto. rewrite replace_head. repeat (rewrite
replace_head'; auto).  constructor; auto.  apply heap_rel_update'. auto. auto.
auto. auto. auto. auto.  auto. crush. auto. crush. 
simpl in X0. destruct c'. apply heap_rel_update' with (l':=l) (v:=close t''
e'') (il':=l') (ep':=ie'') (ip':=ip'') in X0. 
rewrite update_head'; auto. repeat (rewrite replace_head'; auto). 
rewrite update_head' in X0; auto.  repeat (rewrite replace_head' in X0;
auto).    
edestruct IHX . eapply heap_rel_update' in X. eapply X. 
edestruct update_head_exists. rewrite e1 in *. 
edestruct (@replace_head_exists nat). rewrite e2 in *. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2 in *. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2 in *. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2 in *. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2 in *. clear e2. 
edestruct (@replace_head_exists nat). rewrite e2 in *. clear e2. 
edestruct IHX. invert X0. invert e1.  
*)
Lemma env_eq_update' : ∀ Φ p ih l il e ep ip c ie ine' ie' ip' t ne e', 
  clos_eq c Φ ip ep p ih →
  heap_rel l e' ne t il ip' ie' ine' Φ ih →  
  env_eq' e Φ p ie ih →
  env_eq' e (update Φ l c) p ie
    (replace beq_nat (S il) ep (replace beq_nat il ip ih)).
intros. invert X. induce X1. constructor. eapply heap_rel_update' in h0.
econstructor. apply h0. assumption. eapply IHX1_1. apply X0. assumption.
assumption. eapply IHX1_2. apply X0. assumption. assumption. rewrite
update_head. rewrite replace_head. rewrite replace_head'; auto. rewrite
replace_head'; auto. rewrite replace_head. rewrite
replace_head'; auto. rewrite replace_head'; auto. induce X1. constructor. induce
h0. invert H1. invert H2. eapply en. constructor; auto. assumption. assumption.  
eapply en. constructor. induce h0. invert H1. invert H2.  constructor; auto. eapply IHh0.
apply p0. apply X1_1. induce X1. constructor. econstructor. 
crush. constructor;
auto. invert X1. 
crush.  
econstructor. apply heap_tail. constructor. constructor. induce X1. constructor. induce h0; intros. 
constructor. 
 subst.  unfold update. rewrite <- beq_nat_refl.
apply heap_head. constructor.
induce X1; intros. apply e0. apply lu_update_none; auto.  simpl.
apply lu_replace_none; auto. apply lu_replace_none. auto. eapply en.   


simpl in *. 
induce h0. 
eapply en. 
induce h0. 
apply luhdestruct (eq_nat_dec n l).
- subst. econstructor. eapply lookup_update. apply e0.      
Admitted.
*)

Lemma env_eq_fresh' : ∀ e Φ p ep ih f f' ip0 ep0 ne0 t e' ne',
  env_eq' e Φ p ep ih → 
  f > 0 →
  f ∉ domain Φ →
  f' ∉ domain ih →
  (1+f') ∉ domain ih →
  (2+f') ∉ domain ih →
  env_eq' e ((f, cl (close t e') ne')::Φ) p ep ((f',ip0)::(1+f',ep0)::(2+f',ne0)::ih).
intros. induce X. apply e0. eapply en. 
destruct (heap_rel_lookup _ _ _ _ _ _ _ _ _ _ h0). 
destruct p1. destruct p1. 
apply lookup_domain in e3.
apply lookup_domain in e4. 
apply lookup_domain in e2. 
apply lookup_domain in e1. 
constructor; try (apply neq_sym). 
eapply in_notin_neq. apply e3. apply H0.  
eapply in_notin_neq. apply e4. apply H1. 
eapply in_notin_neq. apply e4. apply H2. 
eapply in_notin_neq. apply e4. apply H3. 
eapply in_notin_neq. apply e2. apply H1. 
eapply in_notin_neq. apply e1. apply H1. 
apply h0. assumption. 
apply IHX1; auto. 
apply IHX2; auto. 
Qed.

Lemma env_eq_fresh : ∀ e Φ p ep c ih f f' ip0 ep0 ne0,
  env_eq e Φ p ep ih →
  f ∉ domain Φ →
  f' ∉ domain ih →
  (1+f') ∉ domain ih →
  (2+f') ∉ domain ih →
  env_eq f ((f, c)::Φ) p f' ((f',ip0)::(1+f',ep0)::(2+f',ne0)::ih) →
  env_eq e ((f, c)::Φ) p ep ((f',ip0)::(1+f',ep0)::(2+f',ne0)::ih).
intros. induce X. simpl. destruct c0. eapply ee. invert X0. intros. destruct (eq_nat_dec n
f). subst. rewrite lookup_head in H3. invert H3. subst. 
rewrite lookup_head' in H3; auto.
repeat (rewrite lookup_head'; auto). apply p0. apply H3. apply lookup_domain in e1. eapply in_notin_neq. apply e1.  assumption.
rewrite lookup_head'. rewrite lookup_head'. rewrite lookup_head'. apply e2.
eapply in_notin_neq. apply lookup_domain in e1. apply e1. assumption. 
eapply in_notin_neq. apply lookup_domain in e1. apply e1. assumption.  
eapply in_notin_neq. apply lookup_domain in e1. apply e1. assumption.  
rewrite lookup_head'. rewrite lookup_head'. rewrite lookup_head'. apply e2. 
eapply in_notin_neq. apply lookup_domain in e2. apply e2. auto. 
eapply in_notin_neq. apply lookup_domain in e2. apply e2. auto. 
eapply in_notin_neq. apply lookup_domain in e2. apply e2. auto. 
rewrite lookup_head'. rewrite lookup_head'. rewrite lookup_head'. apply e3. 
eapply in_notin_neq. apply lookup_domain in e3. apply e3. auto. 
eapply in_notin_neq. apply lookup_domain in e3. apply e3. auto. 
eapply in_notin_neq. apply lookup_domain in e3. apply e3. auto. 
assumption. apply IHX1; auto. 
apply IHX2; auto. 
Qed.

Lemma cesm_im : ∀ v s s', 
  state_rel s s' → 
  cesm.step s v → 
  sigT (λ v', prod (refl_trans_clos im.step s' v') (state_rel v v')).
intros v s s' r h. induce h. 
- invert r. invert X. simpl in *. invert X0. destruct s'. simpl in *. subst.  
  exists (st (upd R1 ep st_rf) st_p is 
    (replace beq_nat (1 + ep) (im.ep st_rf) (replace beq_nat ep (ip st_rf) st_h))). 
  split.  
  + destruct st_rf; simpl in *. 
    invert H6.  destruct (skipn ip st_p) eqn:snip. invert H0. 
    invert H0.  destruct l0. invert H2. invert H2. 
    eapply t_step. 
    eapply enter.
    constructor. 
    apply skipn_nth_error in snip.
    simpl. eapply snip. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    eapply write_reg. 
    econstructor. 
    econstructor. 
    econstructor. 
    apply skipn_nth_error_1 in snip.
    apply snip. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    apply t_refl. 
  + destruct st_rf; simpl in *. induce X1. 
      destruct (eq_nat_dec n l). 
    * subst. constructor; simpl. constructor. assumption. econstructor. 
      eapply lookup_update. apply e0. 
      destruct (eq_nat_dec p (S ep)). 
      ** subst.  eapply lookup_replace. apply lookup_replace'. apply e1. auto.
      ** apply lookup_replace'. 
         destruct (eq_nat_dec p ep). subst. eapply lookup_replace.  apply
         (lookup  destruct induce X1. 
  assumption.*)
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
      constructor. eapply step_mov. simpl. eapply read_mem. simpl. apply H0.  constructor.
      eapply step_mov. constructor. simpl. apply H1. constructor.  eapply
      step_jump. constructor. constructor. simpl. eapply t_refl.  
    + constructor; simpl. constructor. assumption. assumption. constructor;
      auto.   
  * simpl in e0. destruct (lookup e Φ) eqn:lue. destruct c0. eapply (IHv _ _ _ _
    _ _ e0). invert e0.  
- destruct s'. invert r. simpl in *. invert X. invert X0. destruct st_rf. simpl
  in *. destruct (new 3 st_h) as [f' ff']. exists (st (mkrf (3+ip0) f' ip f')
  st_p is ((f',ip)::(1+f',ep)::(2+f',ep0)::st_h)). split. 
  + eapply t_step. eapply enter; simpl. constructor. simpl. invert H6. destruct
  (skipn ip0 st_p) eqn:skip. invert H0. invert H0. apply skipn_nth_error in
  skip. apply skip. eapply step_pop. constructor. eapply step_jumpS.
  simpl. apply H5. simpl. eapply (read_reg R1 (st (mkrf ip0 ep0 ip r2) st_p (ep::is) st_h)). 
  constructor. constructor. simpl. eapply t_step. eapply enter. constructor. 
  simpl. invert H6. destruct (skipn ip0 st_p) eqn:skip. invert H0. destruct l.
  invert H0. destruct l. invert H0. invert H0. apply skipn_nth_error_2 in skip.
  apply skip. eapply step_new. apply ff'. econstructor. repeat (econstructor).
  unfold rff. unfold upd. unfold im.r2. unfold st_rf. unfold im.ep. unfold
  im.r1. unfold zeroes. unfold app. rewrite (fresh_closure ip ep ep0 f'). apply
  t_refl. apply ff'.
  + constructor; simpl. constructor. unfold prog_eq. invert H6. destruct (skipn
    ip0 st_p) eqn:sn. invert H0. invert H0. destruct l. invert H2. invert H2.
    destruct l. invert H1. invert H1. rewrite H2 at 1. f_equal. symmetry. eapply
    skipn_3_skipn. apply sn. destruct c. econstructor. rewrite lookup_head.
    reflexivity. apply lookup_head. simpl. rewrite lookup_head'; auto. apply
    lookup_head. rewrite lookup_head'; auto. rewrite lookup_head'; auto. apply
    lookup_head. simpl. crush. crush. invert X. assumption. apply env_eq_fresh;
    auto. invert X. assumption. apply (ff' 0). auto. apply env_eq_fresh; auto. 
    apply (ff' 0). auto. induction X2. constructor. constructor. apply IHX2;
    auto. constructor. assumption. destruct c1. constructor. assumption.
    apply env_eq_fresh; auto. apply (ff' 0). auto. apply IHX2; auto. 
- invert r. invert X. destruct s'. simpl in *. destruct st_rf. simpl in *.
  invert H6. destruct (skipn ip st_p) eqn:skip. invert H0. remember (skipn_nth_error
  _ _ _ _ skip). clear Heqe0. exists (st (mkrf (S ip) ep r1 r2) st_p (S ip + length (assemble
  m (S ip))::ep::st_s) st_h). invert H0. split. 
  + eapply t_step.  
    econstructor. 
    constructor.
    simpl. apply e0.  
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor.
    econstructor. 
    apply t_refl.  
  + constructor; simpl. constructor. unfold prog_eq. apply firstn_app_length in
    H2. destruct H2. rewrite H at 1. simpl. induction st_p. destruct ip. invert
    skip. invert skip. destruct ip. invert skip. simpl. reflexivity. simpl in
    skip. apply skipn_cons' in skip.  rewrite skip. reflexivity. assumption.
    constructor. apply Gt.gt_Sn_O. constructor; auto. unfold prog_eq. apply
    firstn_app_length in H2. destruct H2. apply skipn_cons' in skip. subst.
    rewrite H0 at 1. f_equal. rewrite skipnm_add. rewrite PeanoNat.Nat.add_comm.
    simpl. reflexivity. assumption. 
Admitted.


(*
Lemma cesm_im_assemble : ∀ t v v', 
  refl_trans_clos cesm.step (cesm.I t) v → 
  refl_trans_clos im.step (im.I (assemble t 1)) v'.
*)


