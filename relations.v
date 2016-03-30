Require Import Unicode.Utf8. 

Definition relation (X : Type) (Y : Type) := X → Y → Prop.

Definition transition (X : Type) := X → X → Prop.

Definition deterministic {A} (step : transition A) := ∀ a b c, 
  step a b → 
  step a c →
  b = c
.

Definition strong_bisim (A B : Type) (fa : transition A) (fb : transition B) (R : relation A B) :
  Prop := ∀ a b, R a b → 
          (∀ a', fa a a' → ∃ b', fb b b' ∧ R a' b')
        ∧ (∀ b', fb b b' → ∃ a', fa a a' ∧ R a' b'). 

Inductive refl_trans_clos {X} (f : transition X) : transition X := 
  | t_refl (x : X) : refl_trans_clos f x x
  | t_step (x y z : X) : f x y → refl_trans_clos f y z → refl_trans_clos f x z.

Inductive refl_trans_clos' {X} (f : transition X) : transition X :=
  | t_refl' (x : X) : refl_trans_clos' f x x
  | t_step' (x y z : X) : refl_trans_clos' f x y → f y z → refl_trans_clos' f x z. 

Lemma refl_trans_clos_app {X} : ∀ (f : transition X) (x y z : X), 
  refl_trans_clos f x y → refl_trans_clos f y z → refl_trans_clos f x z. 
intros. induction H. auto. apply IHrefl_trans_clos in H0. rename y into Y. apply
t_step with (y:=Y); auto. Qed. 

Lemma refl_trans_clos'_app {X} : ∀ (f : transition X) (x y z : X), 
  refl_trans_clos' f x y → refl_trans_clos' f y z → refl_trans_clos' f x z. 
intros. induction H0. auto. apply IHrefl_trans_clos' in H. rename y into Y.
apply t_step' with (y:=Y). assumption. assumption. Qed.

Lemma rtc_eq {X} : ∀ f (x y:X), refl_trans_clos f x y ↔ refl_trans_clos' f x y. 
intros. split; intros. induction H. apply t_refl'. rename y into Y. apply
refl_trans_clos'_app with (y:=Y). apply t_step' with (y:=x). apply t_refl'.
assumption. assumption. induction H. apply t_refl. rename y into Y.  apply refl_trans_clos_app
with (y:=Y). assumption. apply t_step with (y:=z).  assumption. apply t_refl.
Qed.

Lemma t_step2 {X} : ∀ (f : transition X) (x y z : X), f y z → refl_trans_clos f x y →
  refl_trans_clos f x z. 
intros. induction H0. apply t_step with (y:=z). assumption. apply t_refl. apply
IHrefl_trans_clos in H. apply (t_step f x y z); assumption. Qed. 

Definition normal_form {X} (x : X) (t : transition X) := ¬∃ x', t x x'.
Definition normal_form_of {X} (t : transition X) (x x' : X) := t x x' ∧ normal_form x' t.

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

Lemma next_nat_le : ∀ m n, refl_trans_clos next_nat m n ↔ le m n.
intros. split. intros. induction H. auto. inversion H. subst. apply le_S in
IHrefl_trans_clos. apply le_S_n. assumption. intros. induction H. apply t_refl.
apply t_step2 with (y:=m0). apply succ. auto. Qed. 

(* simple bisimulation *)
Theorem bisim_next_nat_eq : strong_bisim nat nat next_nat next_nat eq. 
Proof. unfold strong_bisim. intros. subst. split. intros. apply ex_intro with a'.
split; auto. intros. apply ex_intro with b'. split; auto. Qed. 


