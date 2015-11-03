Require expr expr_db_nat.
Require Import List Datatypes util.
Set Implicit Arguments.

Definition fmap_succ (p : prod nat nat) : prod nat nat := match p with
  | (a,b) => (a, S b)
  end.
  
(* a relation between standard lambda terms and deBruijn-indexed terms*)
Inductive db : expr.tm -> list (prod nat nat) -> expr_db_nat.expr -> Prop :=
  | dbVar : forall bs cs v i, 
      db (expr.var v) (bs ++ (v, i) :: cs) (expr_db_nat.var i)
  | dbAbs : forall bs v b b',
      db b ((v,0) :: map fmap_succ bs) b' ->
      db (expr.abs v b) bs (expr_db_nat.lam b')
  | dbApp : forall m n m' n' bs,
      db m bs m' ->
      db n bs n' ->
      db (expr.app m n) bs (expr_db_nat.app m' n').

Definition deBruijn (t:expr.tm) (e:expr_db_nat.expr) : Prop := db t nil e.

Lemma elem_app : forall x xs ys, elem x (List.app xs ys) <-> 
                                 (elem x xs \/ elem x ys).
intros. induction xs. simpl. split; intros. apply or_intror. assumption.
apply or_false in H. assumption. simpl. rewrite IHxs. split;  intros. rewrite
or_assoc. assumption. rewrite or_assoc in H. assumption. Qed.

Lemma let_inline :forall (b c:prod nat nat),
    (fst (let a := b in c)) = (let a := b in fst c).
    auto. Qed.

Lemma fst_fmap_succ : forall x, fst (fmap_succ x) = fst x.
intros. destruct x. simpl. reflexivity. Qed. 

Lemma fst_map_fmap_succ : forall xs:list (prod nat nat), map (fun x => fst
(fmap_succ x)) xs = map (@fst nat nat) xs.
intros. induction xs. auto. simpl. rewrite IHxs. auto. rewrite fst_fmap_succ.
auto. Qed.  

Theorem db_closed_tm : forall f t e, db t f e -> subset (expr.fvs t) (map (@fst nat nat) f).
  intros. 
  induction H.
  simpl.
  rewrite map_app. 
  simpl. 
  rewrite elem_app. 
  simpl. 
  split. 
  right. left. 
  reflexivity. 
  apply I. 
  simpl. simpl in IHdb. 
  rewrite map_map in IHdb. 
  rewrite fst_map_fmap_succ in IHdb.  
  apply subset_filter_cons. assumption.
  simpl.  
  apply app_subset. split; assumption. 
Qed. 

Definition domain (A B : Type) : list (prod A B) -> list A := map (@fst A B). 

Lemma in_heap : forall (A B : Type) (k : A) (f : list (prod A B)), In k (domain f)
                         -> (exists v, In (k,v) f).
intros. unfold domain in H. apply in_map_iff with (prod A B) A (@fst A B) f k in
H. destruct H.  destruct H. destruct H. destruct x. simpl. apply ex_intro with
b. assumption. Qed. 

(* id = id *)
Lemma ex1 : db (expr.abs 0 (expr.var 0)) nil (expr_db_nat.lam (expr_db_nat.var 0)).
apply dbAbs. simpl. rewrite <- app_nil_l with (prod nat nat) ((0, 0) :: nil).
apply dbVar. Qed.

(* true = true *)
Lemma ex2 : db (expr.abs 0 (expr.abs 1 (expr.var 0))) nil 
               (expr_db_nat.lam (expr_db_nat.lam (expr_db_nat.var 1))).
apply dbAbs.
apply dbAbs. simpl. rewrite <- app_nil_l with (prod nat nat) ((0, 1) :: nil). 
rewrite app_comm_cons.
apply dbVar.
Qed.


