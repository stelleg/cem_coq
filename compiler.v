Require expr expr_db_nat.
Require Import db util assembly.
Require Import Arith.Peano_dec.
Require Import List Datatypes.

(* Function instead of logical relation, not equivalent! Function takes first
value in environment, logical relation takes any. Logical relation wrong? *)

Fixpoint db (tm : expr.tm) (env : list (nat * nat)) : option expr_db_nat.expr := match tm with 
  | expr.var v => match lookup eq_nat_dec v env with
    | Some v' => Some (expr_db_nat.var v')
    | None => None
    end
  | expr.abs v b => match db b ((v, 0):: map (fmap' S) env) with 
    | Some b' => Some (expr_db_nat.lam b')
    | None => None
    end
  | expr.app m n => match db m env with
    | Some m' => match db n env with 
      | Some n' => Some (expr_db_nat.app m' n')
      | None => None
      end
    | None => None
    end
  end.

(* TODO: Assembler from db terms.
Fixpoint assemble (e : expr_db_nat.expr) : program. *)
