Definition relation (X : Type) (Y : Type) := X -> Y -> Prop.
Definition transition (X : Type) := X -> X -> Prop.

Definition bisim {P Q}
                 (R : relation P Q) 
                 (a : transition P) 
                 (b : transition Q) : Prop :=
  forall p q,  R p q -> 
   ((forall p', a p p' -> ex (fun q' => b q q' /\ R p' q')) /\ 
    (forall q', b q q' -> ex (fun p' => a p p' /\ R p' q'))).

(* definition on a single set S = P = Q *)
Definition bisim' {S} (R : relation S S) (a : transition S) := @bisim S S R a a.

(* p and q are bisimilar *)
Notation "p '~' q" := (ex (fun t => let (r, a, b) := t in @bisim _ _ p q r a b)) (at level 30). 

Definition partial_function {X Y: Type} (R: relation X Y) :=
  forall (x : X) (y1 y2 : Y), R x y1 -> R x y2 -> y1 = y2. 

Definition total_function {X Y: Type} {R: relation X Y} :=
  forall x : X, exists y : Y, R x y /\ partial_function R. 

Definition reflexive {X : Type} (R: relation X X) :=
  forall a : X, R a a.

Definition symmetric {X : Type} (R: relation X X) :=
  forall a b : X, (R a b) -> (R b a).

Definition antisymmetric {X: Type} (R: relation X X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Definition transitive {X: Type} (R: relation X X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Definition equivalence {X:Type} (R: relation X X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition partial_order {X:Type} (R: relation X X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Inductive next_nat (n : nat) : nat -> Prop := 
    | succ : next_nat n (S n).

(* simple bisimulation *)
Theorem bisim_next_nat_eq : bisim' eq next_nat. 
Proof. unfold bisim'. unfold bisim. intros. rewrite H. split. intros. split with
(S p). split. rewrite H. apply succ. inversion H0. rewrite H. reflexivity.
intros. split with (S p). split. rewrite H. apply succ. inversion H0. rewrite H.
reflexivity. Qed.


