Require Import Unicode.Utf8.
Require Import Decidable.
Require expr expr_db_nat.
Require Import List Datatypes util.
Require Import FunctionalExtensionality CpdtTactics. 
Require Import Arith.Peano_dec.
Require Import Program.Basics.
Set Implicit Arguments.

(* db.v : used to relate debruijn terms with standard terms *) 

Definition fmap {A B C} (f : B -> C) : A * B -> A * C  := fun x => match x with
  | (a, b) => (a, f b) end. 

Definition fmap' {A B C} (f : A -> C) : A * B -> C * B  := fun x => match x with
  | (a, b) => (f a, b) end. 

(* a relation between standard lambda terms and deBruijn-indexed term, note that
  standard variables are nats as well *)
Inductive db : expr.tm -> list (prod nat nat) -> expr_db_nat.expr -> Prop :=
  | dbVar : forall bs cs v i, 
      db (expr.var v) (bs ++ (v, i) :: cs) (expr_db_nat.var i)
  | dbAbs : forall bs v b b',
      db b ((v,0) :: map (fmap S) bs) b' ->
      db (expr.abs v b) bs (expr_db_nat.lam b')
  | dbApp : forall m n m' n' bs,
      db m bs m' ->
      db n bs n' ->
      db (expr.app m n) bs (expr_db_nat.app m' n').

Axiom dbf : {t | expr.closed t} -> {e | expr_db_nat.closed e}.

(* debruijn relation for closed terms *)
Definition deBruijn (t:expr.tm) (e:expr_db_nat.expr) : Prop := db t nil e.

Lemma let_inline :forall (b c:prod nat nat),
    (fst (let a := b in c)) = (let a := b in fst c).
    auto. Qed.

Definition domain (A B : Type) : list (prod A B) -> list A := map (@fst A B). 

Lemma domain_fmap : forall A B C (f:B->C) (xs:list (A * B)),  domain (map
(fmap f) xs) = domain xs.
intros. induction xs. crush. crush. Qed. 

Theorem db_closed_under : forall f t e, db t f e -> subset (expr.fvs t) (domain f).
intros.  induction H.  simpl.  unfold domain.  rewrite map_app.  simpl.
split.  apply in_or_app.  simpl.  right. left.  reflexivity.  apply I.  simpl.
simpl in IHdb.  rewrite domain_fmap in IHdb. rewrite <-
subset_remove_cons. assumption. simpl. apply app_subset_and. split; assumption.
Qed. 

Theorem db_closed : forall t e, db t nil e -> expr.fvs t = nil.
intros. apply db_closed_under in H. simpl in H. unfold subset in H. destruct
(expr.fvs t).  reflexivity. inversion H. inversion H0. Qed. 

Axiom closed_db_under : forall f t, subset (expr.fvs t) (domain f) -> 
  exists e, db t f e.

(*
Theorem closed_db_under : forall f t, subset (expr.fvs t) (domain f) -> exists
e, db t f e.
intros. induction t. destruct H. apply in_split in H. crush. clear H0.
apply ex_intro with (expr_db_nat.var n).
induction f. crush. induction t. inversion H. inversion H0. unfold expr.fvs
in H. apply app_subset_and in H. destruct H. crush. apply ex_intro with
(expr_db_nat.app x0 x). apply dbApp; assumption. apply ex_intro with
expr_db_nat.lam 
induction e. crush. apply in_split in H0. destruct H0. destruct H.   
induction H. crush. unfold domain. rewrite map_app. rewrite in_app_iff.
right. crush. crush. rewrite <- subset_remove_cons. rewrite domain_fmap in IHdb.
assumption. simpl. apply app_subset_and. crush. Qed. 
*)

Definition lookup' {A B} : forall (f : list (A * B)) (a: {a | In a (domain f)}), B. 
intros. induction f. crush. destruct a. inversion f. destruct a0. assumption.
Qed.

Definition In' {A} := flip (@In A).

Definition sumbool_or {A B} : {A} + {B} -> A \/ B := fun b => match b with
  | left a => or_introl a
  | right b => or_intror b
  end.

Definition inx (x:nat) := In x (domain ((0,1) :: nil)).

Lemma in_heap : forall (A B : Type) (k : A) (f : list (prod A B)), In k (domain f)
                         -> (exists v, In (k,v) f).
intros. unfold domain in H. apply in_map_iff with (prod A B) A (@fst A B) f k in
H. destruct H.  destruct H. destruct H. destruct x. simpl. apply ex_intro with
b. assumption. Qed. 

(* id = id *) Lemma ex1 : db (expr.abs 0 (expr.var 0)) nil (expr_db_nat.lam (expr_db_nat.var 0)).
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


