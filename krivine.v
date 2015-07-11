Require Vector.
Require Import List.
Require Import expr_db.

Inductive closure : Type :=
  | close : forall n, expr n -> Vector.t closure n -> closure.

Definition krivine_state : Type := prod closure (list closure).

Definition krivine (st : krivine_state) : option krivine_state :=
  match st with
  | (close f exp env, args) =>  match exp with
    | var i => Some (Vector.nth env i, args)
    | app m n => Some (close f m env, close f n env :: args)
    | lam b => match args with
      | nil => None 
      | cons a args' => Some (close (S f) b (Vector.cons closure a f env), args')
      end
    end
  end.

Definition krivine_relation : krivine_state -> option krivine_state -> Prop :=
  fun (st : krivine_state) (st' : option krivine_state) => st' = krivine st.

Definition is_value : closure -> bool := fun c => match c with
  | close _ (lam _) _ => true
  | _ => false
  end.

Definition value : closure -> Prop := fun c => is_value c = true.

Theorem krivine_fixed : forall st : krivine_state, krivine_relation st None -> value (fst st).
Proof.
intros. 
destruct st. 
destruct c. 
destruct e. 
inversion H. 
destruct l. 
simpl. unfold value. unfold is_value. reflexivity. 
inversion H. 
inversion H. 
Qed.


