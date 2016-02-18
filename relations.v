Require Import Unicode.Utf8. 

Definition relation (X : Type) (Y : Type) := X → Y → Prop.

Definition transition (X : Type) := X → X → Prop.

Definition strong_bisim (A B : Type) (fa : transition A) (fb : transition B) (R : relation A B) :
  Prop := ∀ a b, R a b → 
          (∀ a', fa a a' → ∃ b', fb b b' ∧ R a' b')
        ∧ (∀ b', fb b b' → ∃ a', fa a a' ∧ R a' b'). 

Inductive refl_trans_clos {X} (f : transition X) : transition X := 
  | t_refl (x : X) : refl_trans_clos f x x
  | t_step (x y z : X) : f x y → refl_trans_clos f y z → refl_trans_clos f x z.

(* p and q are bisimilar *)
Notation "p '~' q" := (∃ fp fq R, strong_bisim p q fp fq R) (at level 30). 

Definition partial_function {X Y: Type} (R: relation X Y) :=
  ∀ (x : X) (y1 y2 : Y), R x y1 → R x y2 → y1 = y2. 

Definition total_function {X Y: Type} (R: relation X Y) :=
  (∀ x:X, ∃ y:Y, R x y) ∧ partial_function R. 

Definition surjective {X Y: Type} (f : X → Y) : Prop :=
  ∀ y:Y, ∃ x:X, f x = y.

Definition injective {X Y : Type} (f : X → Y) : Prop :=
  ∀ a b: X, f a = f b → a = b.

Definition bijective {X Y : Type} (f : X → Y) : Prop :=
  injective f ∧ surjective f.

Definition reflexive {X : Type} (R: relation X X) :=
  ∀ a : X, R a a.

Definition symmetric {X : Type} (R: relation X X) :=
  ∀ a b : X, (R a b) → (R b a).

Definition antisymmetric {X: Type} (R: relation X X) :=
  ∀ a b : X, (R a b) → (R b a) → a = b.

Definition transitive {X: Type} (R: relation X X) :=
  ∀ a b c : X, (R a b) → (R b c) → (R a c).

Definition equivalence {X:Type} (R: relation X X) :=
  (reflexive R) ∧ (symmetric R) ∧ (transitive R).

Definition partial_order {X:Type} (R: relation X X) :=
  (reflexive R) ∧ (antisymmetric R) ∧ (transitive R).

(* Examples *)

Inductive next_nat (n : nat) : nat → Prop := 
    | succ : next_nat n (S n).

(* simple bisimulation *)
Theorem bisim_next_nat_eq : strong_bisim nat nat next_nat next_nat eq. 
Proof. unfold strong_bisim. intros. subst. split. intros. apply ex_intro with a'.
split; auto. intros. apply ex_intro with b'. split; auto. Qed. 


