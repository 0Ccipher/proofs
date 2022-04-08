(* Transaction memory models CCV, CC, CM *)

Require Import ZArith.
Require Import Ensembles.
Require Import util.


Set Implicit Arguments.

Ltac decide_equality := decide equality; auto with equality arith.

Definition Word := nat.

Definition Address := Word.

Definition Value := Word.
Lemma eqValue_dec : forall (x y: Value), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqValue_dec : equality.
(*Hypothesis eqValue_dec : forall (x y: Value), {x=y} + {x <> y}.*)


Definition Proc := nat.
Lemma eqProc_dec : forall (x y: Proc), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqProc_dec : equality.
(*Hypothesis eqProc_dec : forall (x y: Proc), {x=y} + {x <> y}.*)

Definition program_order_index := nat.
Lemma eqPoi_dec : forall (x y: program_order_index), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Global Hint Resolve eqPoi_dec : equality.

Record Iiid  : Set := mkiiid {
  proc : Proc;
  poi: program_order_index }.
Lemma eqIiid_dec : forall (x y: Iiid), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Global Hint Resolve eqIiid_dec : equality.

Check Iiid.

(*Definition Eiid := nat.
Lemma eqEiid_dec : forall (x y: Eiid), {x=y} + {x<>y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqEiid_dec : equality.
*)

Inductive Dirn : Set :=
  | R : Dirn
  | W : Dirn.
Lemma eqDirn_dec : forall (x y: Dirn), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqDirn_dec : equality.

Definition Location := Address.

Lemma eqLoc_dec : forall (x y: Location), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqLoc_dec : equality.


(* Transactions related *)

Definition Tid := nat.

Inductive Tactions : Set :=
  | begint : Tactions
  | endt : Tactions
  | delt : Tactions.

Check Tactions.

 
Lemma eqTactions_dec : forall (x y: Tactions), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqTactions_dec : equality.


Inductive Action : Set :=
  | Access : Dirn -> Location -> Value -> Action
  | Trans : Tactions -> Tid -> Proc -> Action.

Check Action.

Lemma eqAction_dec : forall (x y: Action), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqAction_dec : equality.

Record Event := mkev {
  (* eiid : Eiid; *)
  iiid : Iiid;
  tiid  : Tid;
  action : Action}.

Check Event.

Lemma eqEv_dec : forall (x y: Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqEv_dec : equality.

Lemma eqEvc_dec : forall (x y: Event*Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqEvc_dec : equality.


Lemma eqTid_dec : forall (x y: Tid), {x=y} + {x<>y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqTid_dec : equality.

Record Transaction := mktrans {
  tid : Tid; 
  tevents : set Event;
  tproc : Proc}.


(* Define transaction delivery *)
