Require Import Unicode.Utf8.
Require Import relations.

Record machine (expr : Type) : Type := mkmachine {
  state : Type;
  insert : expr → state; 
  step : transition state
}.
