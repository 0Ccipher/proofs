(* Transaction memory models CCV, CC, CM *)

(* 

 This file defines traces for transactional memories
  
*)

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

Record Iid : Set := mkiid {
  proc : Proc;
  poi  : program_order_index }.
Lemma eqIid_dec : forall (x y: Iid), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Global Hint Resolve eqIid_dec : equality.

Check Iid.

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


Inductive Action : Set :=
  | Access : Dirn -> Location -> Value -> Action.
Lemma eqAction_dec : forall (x y: Action), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqAction_dec : equality.

(*Record Events := mkev{
  actions : set Action}.

Lemma eqEv_dec : forall (x y: Events), {x=y} + {x <> y}. 
Proof. 
decide_equality.
Defined.*)

(* Record Event := mkev { *)
(*   (* eiid : Eiid; *) *)
(*   iid : Iiid; *)
(*   tiid  : Tid; *)
(*   action : Action}. *)

(* Check Event. *)

(* Lemma eqEv_dec : forall (x y: Event), {x=y} + {x <> y}. *)
(* Proof. *)
(* decide_equality. *)
(* Defined. *)
(* Global Hint Resolve eqEv_dec : equality. *)

(* Lemma eqEvc_dec : forall (x y: Event*Event), {x=y} + {x <> y}. *)
(* Proof. *)
(* decide_equality. *)
(* Defined. *)
(* Global Hint Resolve eqEvc_dec : equality. *)


Definition Tid := nat.
Lemma eqTid_dec : forall (x y: Tid), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Global Hint Resolve eqTid_dec : equality.
 
Record Trans := mktrans{
  tid : Tid;
  iid : Iid}.

Lemma eqTr_dec : forall (x y: Trans), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqTr_dec : equality.

Lemma eqTrc_dec : forall (x y: Trans*Trans), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Global Hint Resolve eqTrc_dec : equality.

Record Transaction := mktransaction {
  transaction : Trans; 
  tevents : set Action}.
Check Transaction.

Record Trans_struct : Type := mkts {
  transactions : set Transaction;
  iico : Rln Transaction
}. 

Definition po (ts: Trans_struct) : set (Transaction*Transaction) :=
  fun c => match c with (t1,t2) =>
   (* both transactions belong to same process *)
  (t1.(transaction).(iid).(proc) = t2.(transaction).(iid).(proc)) /\
  (* the program order index of t1 is less than equal to the program order index of t2 *)
  (le t1.(transaction).(iid).(poi) t2.(transaction).(iid).(poi)) /\
  (* both t1 and t2 are in the set of transactions ts *)
  (In _ ts.(transactions) t1) /\
  (In _ ts.(transactions) t2)
  end.
Check po.

Definition po_strict (ts: Trans_struct) : Rln Transaction :=
  fun t1 => fun t2 =>
   (* both transactions belong to same process *)
  (t1.(transaction).(iid).(proc) = t2.(transaction).(iid).(proc)) /\
  (* the program order index of t1 is less than the program order index of t2 *)
  (lt t1.(transaction).(iid).(poi) t2.(transaction).(iid).(poi)) /\
  (* both t1 and t2 are in the set of transactions ts *)
  (In _ ts.(transactions) t1) /\
  (In _ ts.(transactions) t2).
Check po_strict.

Definition po_iico (ts:Trans_struct) : Rln Transaction :=
  fun t1 => fun t2 =>
    (po_strict ts) t1 t2 \/ (iico ts) t1 t2.
Check po_iico.


(* Define traces *)
