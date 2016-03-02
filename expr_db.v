Require expr.
Require Import List Datatypes.
Require Import Arith.Peano_dec.
Require Import db util.

(* Compiles standard expressions to terms with deBruijn indices *)
Fixpoint db (t : expr.tm) (env : Map nat nat) : option tm := match t with 
  | expr.var v => match lookup eq_nat_dec v env with
    | Some v' => Some (var v')
    | None => None
    end
  | expr.abs v b => match db b ((v, 0):: map (fmap S) env) with 
    | Some b' => Some (lam b')
    | None => None
    end
  | expr.app m n => match db m env with
    | Some m' => match db n env with 
      | Some n' => Some (app m' n')
      | None => None
      end
    | None => None
    end
  end.

(* We say two expressions are alpha equivalent if they compile to the same
deBruijn term *)
Definition alpha_equiv (t1 t2 : expr.tm) : Prop := db t1 = db t2.

