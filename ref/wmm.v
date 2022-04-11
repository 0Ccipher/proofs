Require Import ZArith.
Require Import Ensembles.
Require Import util.

Set Implicit Arguments.

Ltac decide_equality := decide equality; auto with equality arith.

Definition Word := nat.

Definition Address := Word.

Definition Value := Word.
Hypothesis eqValue_dec : forall (x y: Value), {x=y} + {x <> y}.
(*Hint Resolve eqValue_dec : equality.*)

Definition Proc := nat.
Hypothesis eqProc_dec : forall (x y: Proc), {x=y} + {x <> y}.
(*Hint Resolve eqProc_dec : equality.*)

Definition program_order_index := nat.
Lemma eqPoi_dec : forall (x y: program_order_index), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Hint Resolve eqPoi_dec : equality.

Record Iiid  : Set := mkiiid {
  proc : Proc;
  poi: program_order_index }.
Lemma eqIiid_dec : forall (x y: Iiid), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
(*Hint Resolve eqIiid_dec : equality.*)

Definition Eiid := nat.
Lemma eqEiid_dec : forall (x y: Eiid), {x=y} + {x<>y}.
Proof.
decide_equality.
Defined.
(*Hint Resolve eqEiid_dec : equality.*)

Inductive Dirn : Set :=
  | R : Dirn
  | W : Dirn.
Lemma eqDirn_dec : forall (x y: Dirn), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqDirn_dec.

Definition Location := Address.

Lemma eqLoc_dec : forall (x y: Location), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqLoc_dec : equality.

Inductive Action : Set :=
  | Access : Dirn -> Location -> Value -> Action.
Lemma eqAction_dec : forall (x y: Action), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqAction_dec : equality.

Record Event := mkev {
  eiid : Eiid; 
  iiid : Iiid;
  action : Action}.
Lemma eqEv_dec : forall (x y: Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEv_dec : equality.

Lemma eqEvc_dec : forall (x y: Event*Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEvc_dec : equality.

(*Module OEEvt.
Parameter LE : Rln Event -> Rln Event.
Hypothesis OE : forall (s S:set Event) (r:Rln Event),
  Included _ s S ->
  partial_order r s -> 
  rel_incl r (LE r) /\
  linear_strict_order (LE r) S.
Hypothesis le_lso : forall (s:set Event) (r:Rln Event),
  linear_strict_order r s -> LE r = r.
End OEEvt.
Import OEEvt.*)

Record Event_struct : Type := mkes {
  events : set Event;
  iico : Rln Event}. 

Definition po (es: Event_struct) : set (Event*Event) :=
  fun c => match c with (e1,e2) =>
   (* both events have same processor *)
  (e1.(iiid).(proc) = e2.(iiid).(proc)) /\
  (* the program order index of e1 is less than the program order index of e2 *)
  (le e1.(iiid).(poi) e2.(iiid).(poi)) /\
  (* both e1 and e2 are in the events of e *)
  (In _ es.(events) e1) /\
  (In _ es.(events) e2)
  end.

Definition po_strict (es: Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
   (* both events have same processor *)
  (e1.(iiid).(proc) = e2.(iiid).(proc)) /\
  (* the program order index of e1 is less than the program order index of e2 *)
  (lt e1.(iiid).(poi) e2.(iiid).(poi)) /\
  (* both e1 and e2 are in the events of e *)
  (In _ es.(events) e1) /\
  (In _ es.(events) e2).

Definition po_iico (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    (po_strict E) e1 e2 \/ (iico E) e1 e2.

Definition loc (e:Event) : (*option*) Location :=
match e.(action) with
  | Access _ l _ => (*Some*) l
end. 

Definition value_of (e:Event) : (*option*) Value :=
  match e.(action) with
  | Access _ _ v => (*Some*) v
  end.

Definition proc_of (e:Event) : Proc := e.(iiid).(proc). 

Definition procs (es: Event_struct) : set Proc := 
   fun p => exists e, 
     In _ es.(events) e /\ 
     p = proc_of e. 

Definition to_shared (s:set Event) : set (Event) :=
  fun e => In _ s e /\ exists l, exists a, l = a /\ loc e = (*Some*) l.

Definition reads (es:Event_struct) : set Event :=
  fun e => (In _ es.(events) e) /\ (exists l, exists v, e.(action) = Access R l v). 

Definition writes (es:Event_struct) : set Event :=
  fun e => (In _ es.(events) e) /\ (exists l, exists v, e.(action) = Access W l v).

Definition po_loc (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 => loc e1 = loc e2 /\ po_iico E e1 e2.
Definition po_loc_llh (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 => loc e1 = loc e2 /\ po_iico E e1 e2 /\
    ~(reads E e1 /\ reads E e2).

Definition well_formed_event_structure (E:Event_struct) : Prop :=
  (forall x y, po_iico E x y -> proc_of x = proc_of y) /\
  (forall e1 e2, In _ E.(events) e1 -> In _ E.(events) e2 ->
   (e1.(eiid) = e2.(eiid)) /\ (e1.(iiid) = e2.(iiid)) -> (e1 = e2)) /\
   Included _ (dom (iico E)) E.(events) /\
   Included _ (ran (iico E)) E.(events) /\
   acyclic (iico E) /\ (forall x y, events E x /\ events E y /\ poi (iiid x) = poi (iiid y) /\ proc_of x = proc_of y -> x <> y -> iico E x y) /\
    (forall e1 e2, (iico E) e1 e2 -> (e1.(iiid) = e2.(iiid))) /\
   trans (iico E).

Definition Coherence := Rln Event.

Definition write_to (e:Event) (l:Location) : Prop :=
  exists v, action e = Access W l v.

Definition writes_to_same_loc_l (s:set Event) (l:Location) : set Event :=
  fun e => In _ s e /\ write_to e l.

Definition coherence_well_formed (s:set Event) (co:Coherence) : Prop :=
  (forall l, linear_strict_order 
     (rrestrict co (writes_to_same_loc_l s l)) (writes_to_same_loc_l s l)) (*Hws_tot*) /\
  (forall x e, co x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l s l) x /\
    In _ (writes_to_same_loc_l s l) e)) (*Hws_cands*).
Definition write_serialization_well_formed (s:set Event) (co:Coherence) := 
  coherence_well_formed s co.

Ltac destruct_ws H :=
  destruct H as [Hws_tot Hws_cands].

Definition Rfmap := Rln Event.

Definition read_from (e:Event) (l:Location) : Prop :=
  exists v, action e = Access R l v.

Definition rfmaps (s:set Event) : Rln Event :=
  fun e1 => fun e2 =>
  In _ s e1 /\ In _ s e2 /\
  exists l, write_to e1 l /\ read_from e2 l /\ 
    value_of e1 = value_of e2.

Definition no_intervening_write (e1 e2:Event) (s:Rln Event): Prop :=
  s e1 e2 /\
  forall l, write_to e1 l ->
    ~(exists e3, write_to e3 l /\ s e1 e3 /\ s e3 e2).

Definition ls (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    In _ (reads E) e1 /\ In _ (writes E) e2 /\ (po_iico E) e1 e2.

Definition rfmaps_well_formed (E:Event_struct) (s:set Event) (rf:Rfmap) : Prop :=
  (forall er, In _ (reads E) er -> exists ew, 
     ((In _ s ew) /\ rf ew er)) /\ (*Hrf_init*) 
  (forall e1 e2, rf e1 e2 -> (rfmaps s) e1 e2) /\ (*Hrf_cands*) 
   (forall x w1 w2, rf w1 x -> rf w2 x ->
    w1 = w2).  (*Hrf_uni*)

Ltac destruct_rf H :=
  destruct H as [Hrf_init [Hrf_cands Hrf_uni]].

Definition Frmap := Rln Event.

Definition frmaps (s:set Event) (rf:Rfmap) (co:Coherence) : Frmap :=
  fun er => fun ew => In _ s er /\ In _ s ew /\
    exists wr, rf wr er /\ co wr ew.

Definition AB := Rln Event. 

Definition ab_well_formed (s:set Event) (abc : AB) :=
  (forall x y, abc x y -> In _ s x /\ In _ s y /\ x<>y).

Record Execution_witness : Type := mkew {
  co : Coherence;
  rf : Rfmap}.
Definition ws X := co X.

Definition fr (E:Event_struct) (X:Execution_witness) : Frmap :=
  frmaps (events E) (rf X) (co X).
Definition rfi (X:Execution_witness) : Rfmap :=
  fun ew => fun er => (rf X) ew er /\ proc_of ew = proc_of er.
Definition rfe (X:Execution_witness) : Rfmap :=
  fun ew => fun er => (rf X) ew er /\ proc_of ew <> proc_of er.

Definition com (E:Event_struct) (X:Execution_witness) : Rln Event :=
  rel_union (rel_union (rf X) (fr E X)) (co X).

Module Type Dp.
Parameter dp : Event_struct -> Rln Event.
Hypothesis dp_valid : forall (E:Event_struct),
  rel_incl (dp E) (po_iico E) /\ trans (dp E) /\
  forall x y, dp E x y -> reads E x.
(*Hypothesis dp_fun :
  forall E s x y,
  dp E x y /\ s x /\ s y <->
  dp (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.*)
End Dp.

Set Implicit Arguments.
Definition rfc (A:Type) (rfe:Rln A) (r:Rln A) :=
  rel_union r (rel_union (rel_seq rfe r) (rel_union (rel_seq r rfe) (rel_seq rfe (rel_seq r rfe)))).
Unset Implicit Arguments.

Module Type Archi.
Parameter llh : bool.
Parameter ppo : Event_struct -> Rln Event.
Hypothesis ppo_valid : forall (E:Event_struct),
  rel_incl (ppo E) (po_iico E).
Parameter fences : Event_struct -> Rln Event.
Hypothesis fences_valid : forall (E:Event_struct),
  rel_incl (fences E) (po_iico E).
Parameter prop : Event_struct -> Execution_witness -> Rln Event.
Hypothesis prop_valid : forall E X, ~(exists x, (prop E X) x x).
Hypothesis prop_trans : forall E X, trans (prop E X).
Hypothesis wit_incl :
  forall E X X' e1 e2,
  ((rf X) e1 e2 -> (rf X') e1 e2) ->
  prop E X e1 e2 ->
  prop E X' e1 e2.
End Archi.

Module Wmm (A : Archi) (dp : Dp).
Import A.
Import dp.

Definition hb (E:Event_struct) (X:Execution_witness) : Rln Event :=
  rel_union (rfe X) (tc (rel_union (A.ppo E) (A.fences E))).

Definition com' (E:Event_struct) (X:Execution_witness) : util.Rln Event :=
  fun e1 => fun e2 => (rel_union (rel_union (com E X) (rel_seq (ws X) (rf X))) (rel_seq (fr E X) (rf X))) e1 e2.

Definition com_vs_po E X (r:Rln Event) :=
  (forall e1 e2, r e1 e2 -> ~(com' E X e2 e1)).

Definition uniproc E X :=
  (*if llh then*) com_vs_po E X (po_loc_llh E)
  (*else com_vs_po E X (po_loc E)*).

Definition valid_execution (E:Event_struct) (X:Execution_witness) : Prop :=
  coherence_well_formed (events E) (co X) /\
  rfmaps_well_formed E (events E) (rf X) /\
  uniproc E X /\
  acyclic (hb E X) /\ (*<<< would need irrefl(hb) for C++ as of today*)
  irrefl (rel_seq (fr E X) (rel_seq (prop E X) (hb E X))) /\
  acyclic (rel_union (co X) (prop E X)).

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Huni [Hth [Hlc Hvalid]]]]]; 
  unfold coherence_well_formed in Hws_tot(*; unfold uniproc in Hsp*).

(*Goal forall E X, valid_execution E X -> True.
intros E X Hvalid.
destruct_valid Hvalid. *)

End Wmm.