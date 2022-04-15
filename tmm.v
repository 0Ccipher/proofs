(* Transaction memory models CCV, CC, CM *)

(* 

 This file defines traces for transactional memories
  
*)


Require Import ZArith.
Require Import Ensembles.
Require Import TMM.util.


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

(* tdo: Why do we need po?*)
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


Definition po_or_iico (ts:Trans_struct) : Rln Transaction :=
  fun t1 => fun t2 =>
    (po_strict ts) t1 t2 \/ (iico ts) t1 t2.


Definition reads (ts:Trans_struct) : set Transaction :=
  fun t => (In _ ts.(transactions) t) /\ (exists l, exists v, In _ t.(tevents) (Access R l v)). 

Definition writes (ts:Trans_struct) : set Transaction :=
  fun t => (In _ ts.(transactions) t) /\ (exists l, exists v, In _ t.(tevents) (Access W l v)). 


Definition well_formed_trans_structure (ts:Trans_struct) : Prop :=
  (forall x y, po_or_iico ts x y -> x.(transaction).(iid).(proc) = y.(transaction).(iid).(proc)) /\
  (forall t1 t2, In _ ts.(transactions) t1 -> In _ ts.(transactions) t2 ->
   (t1.(transaction).(tid) = t2.(transaction).(tid)) /\ 
   (t1.(transaction).(iid) = t2.(transaction).(iid)) -> (t1 = t2)) /\
   Included _ (dom (iico ts)) ts.(transactions) /\
   Included _ (ran (iico ts)) ts.(transactions) /\
   acyclic (iico ts) /\ 
   (forall x y, transactions ts x /\ transactions ts y /\ 
      x.(transaction).(iid).(poi) = x.(transaction).(iid).(poi)
     /\ x.(transaction).(iid).(proc) = y.(transaction).(iid).(proc) -> x <> y -> iico ts x y) /\
   (forall t1 t2, (iico ts) t1 t2 -> (t1.(transaction).(iid) = t2.(transaction).(iid))) /\
   trans (iico ts).

(* Coherence Order *)
Definition Coherence := Rln Transaction.
Check Coherence.

Definition write_to_loc_l (t:Transaction) (l:Location) : Prop :=
  exists v, In _ t.(tevents) (Access W l v).

Definition writes_to_same_loc_l (s:set Transaction) (l:Location) : set Transaction :=
  fun t => In _ s t /\ write_to_loc_l t l.

Check writes_to_same_loc_l.

Definition coherence_well_formed (s:set Transaction) (co:Coherence) : Prop :=
  (forall l: Location, linear_strict_order 
     co (writes_to_same_loc_l s l)) (*Hws_tot*) /\
  (forall x e, co x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l s l) x /\
    In _ (writes_to_same_loc_l s l) e)) (*Hws_cands*).

Definition rrestrict_ts (A:Type) (r:Rln A) (s:set A) : Rln A := 
    fun x => fun y =>
    r x y /\ In _ s x /\ In _ s y.

Definition coherence_well_formed_rrestrict (s:set Transaction) (co:Coherence) : Prop :=
  (forall l: Location, linear_strict_order 
     (rrestrict_ts co (writes_to_same_loc_l s l)) (writes_to_same_loc_l s l)) (*Hws_tot*) /\
  (forall x e, co x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l s l) x /\
    In _ (writes_to_same_loc_l s l) e)) (*Hws_cands*).

Definition write_serialization_well_formed (s:set Transaction) (co:Coherence) := 
  coherence_well_formed s co.

Definition Rfmap := Rln Transaction.

Definition has_read_on_l (t:Transaction) (l:Location) : Prop :=
  exists v, In _ t.(tevents) (Access R l v).

Definition rfmaps (ts:set Transaction) : Rln Transaction :=
  fun t1 => fun t2 =>
  In _ ts t1 /\ In _ ts t2 /\
  exists l:Location, exists v: Value,exists wact:Action, exists ract:Action ,
    wact = Access W l v /\ ract = Access R l v /\
    In _ t1.(tevents) wact /\ In _ t2.(tevents) ract.

Definition no_intervening_write (t1 t2:Transaction) (ts:Rln Transaction): Prop :=
  ts t1 t2 /\
  forall l, write_to_loc_l t1 l ->
    ~(exists t3, write_to_loc_l t3 l /\ ts t1 t3 /\ ts t3 t2).

Definition ls (ts:Trans_struct) : Rln Transaction :=
  fun t1 => fun t2 =>
    In _ (reads ts) t1 /\ In _ (writes ts) t2 /\ (po_or_iico ts) t1 t2.

Definition rfmaps_well_formed (ts:Trans_struct) (s:set Transaction) (rf:Rfmap) : Prop :=
  (forall tr, In _ (reads ts) tr -> exists tw, 
     ((In _ s tw) /\ rf tw tr)) /\ (*Hrf_init*) 
  (forall t1 t2, rf t1 t2 -> (rfmaps s) t1 t2) /\ (*Hrf_cands*) 
   (forall tr tw1 tw2, rf tw1 tr -> rf tw2 tr ->
    tw1 = tw2).(*Hrf_uni*)

