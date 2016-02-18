Require expr expr_db_nat cbn cem cesm.
Require Import db util assembly.
Require Import Arith.Peano_dec.
Require Import List Datatypes.
Require Import Unicode.Utf8.

(* This file has the high level structure of the compiler and the corresponding
main theorems of correctness *)

Definition compile (t : expr.tm) : option Program := match db t nil with
  | Some a => Some (assemble a)
  | None => None 
  end.

(* Definition compile (t: expr.tm) : expr.closed t → { mc | trans_clos prog p }.
*)

