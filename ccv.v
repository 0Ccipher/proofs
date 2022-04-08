(* 

 This file defines ccv executions

*)


Require Import ZArith.
Require Import Ensembles.
Require Import util.


Inductive Tactions : Set :=
  | begint : Tactions
  | endt : Tactions
  | delt : Tactions.
Lemma eqTactions_dec : forall (x y: Tactions), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqTactions_dec : equality.

Check Tactions.
