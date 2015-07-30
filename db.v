Require expr expr_db_nat.
Require Import List Datatypes.

(* a relation between standard lambda terms and deBruijn-indexed terms*)
Inductive db : expr.tm -> list (prod expr.id nat) -> expr_db_nat.expr -> Prop :=
  | dbVar : forall bs cs v i, 
      db (expr.var v) (bs ++ (v, i) :: cs) (expr_db_nat.var i)
  | dbAbs : forall bs v b b',
      db b ((v,0) :: map (fun (p : prod expr.id nat) => let (a,b) := p in (a,S b)) bs) b' ->
      db (expr.abs v b) bs (expr_db_nat.lam b')
  | dbApp : forall m n m' n' bs,
      db m bs m' ->
      db n bs n' ->
      db (expr.app m n) bs (expr_db_nat.app m' n').

Definition deBruijn (t:expr.tm) (e:expr_db_nat.expr) : Prop := db t nil e.

(* id = id *)
Lemma ex1 : db (expr.abs 0 (expr.var 0)) nil (expr_db_nat.lam (expr_db_nat.var 0)).
apply dbAbs. simpl. rewrite <- app_nil_l with (prod expr.id nat) ((0 : expr.id, 0) :: nil).
apply dbVar. Qed.

(* true = true *)
Lemma ex2 : db (expr.abs 0 (expr.abs 1 (expr.var 0))) nil 
               (expr_db_nat.lam (expr_db_nat.lam (expr_db_nat.var 1))).
apply dbAbs.
apply dbAbs. simpl. rewrite <- app_nil_l with (prod expr.id nat) ((0 : expr.id, 1) :: nil). 
rewrite app_comm_cons.
apply dbVar.
Qed.

