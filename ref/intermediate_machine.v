Require Import ZArith.
Require Import Ensembles.
Require Import List.
Require Import Bool.
Require Import util.
Require Import wmm.
Require Import basic.

Module Machine (A:Archi) (dp:Dp).
Import dp.
Inductive DEvent : Set :=
  | DR : Event*Event -> DEvent
  | DW : Event -> DEvent.
Lemma eqDEvt_dec : forall (x y:DEvent), {x=y}+{x<>y}.
Proof.
intros x y; decide_equality.
Defined.
Hint Resolve eqDEvt_dec : equality.
Inductive Label : Set :=
  | d : DEvent -> Label
  | f : DEvent -> Label.
Lemma eqLabel_dec : forall (x y:Label), {x=y}+{x<>y}.
Proof.
intros x y; decide_equality.
Defined.
Hint Resolve eqLabel_dec : equality.

Parameter dB : Event.
Hypothesis dB_not_in_E :
  forall E e, events E e -> e <> dB.
Hypothesis dB_loc :
  forall l, loc dB = l.
Hypothesis dB_not_ran : 
  forall B, ~(ran B dB).
Hypothesis udr_dB :
  forall B e, (udr B e <-> rrestrict B (fun w => loc w = loc e) dB e).

Definition Buffer := Rln Event.
Definition wf_buff (E:Event_struct) (B:Buffer) := 
  (forall w, udr B w -> w <> dB -> writes E w) /\
  (forall w1 w2, events E w1 -> events E w2 -> w1 <> w2 -> ran B w1 -> ran B w2 -> loc w1 = loc w2 -> B w1 w2 \/ B w2 w1) /\
  (forall e, acyclic (rrestrict B (fun w => loc w = loc e))) /\
  trans B /\
  (forall w1 w2, B w1 w2 -> w1 <> dB -> loc w1 = loc w2).

Definition ESet := set Event. 
Definition wf_ws (E:Event_struct) (B:ESet) :=
  forall e, B e -> writes E e. 
Definition wf_rs (E:Event_struct) (R:ESet) :=
  forall e, R e -> reads E e. 
Definition wf_rcp (E:Event_struct) (Rcp:ESet) :=
  forall e, Rcp e -> writes E e. 

Record State := mks {
  B : ESet; (*faire de B un ensemble seulement*)
  Rcp : Buffer;
  Rs : ESet;
  Cs : ESet
}.

Parameter bin : set Event -> Event -> bool.

Hypothesis In_bin :
  forall (r : set Event) e,
  r e -> bin r e = true.
Hypothesis bin_In :
  forall (r : set Event) e,
  bin r e = true -> r e.
Hypothesis nbin_nIn :
  forall (r : set Event) e,
  bin r e = false -> ~r e.
Hypothesis nIn_nbin :
  forall (r : set Event) e,
  ~r e -> bin r e = false.

Definition upd_buff (B:Buffer) (e:Event): Buffer :=
  if bin (udr B) e then B else
  rel_union B (fun e1 => fun e2 => (e1 = dB \/ (ran B e1 /\ loc e1 = loc e)) /\ e2 = e).  

Definition upd_rs (R:ESet) e: ESet :=
  Union _ R (fun r => r = e).

Definition del_buff (B:Buffer) (e:Event): Buffer :=
  (fun e1 => fun e2 => B e1 e2 /\ e1 <> e /\ e2 <> e).

Definition del_rs (R:ESet) (e:Event) : ESet :=
  (fun r => R r /\ r <> e).

Parameter bemp : Rln Event -> bool.
Hypothesis bemp_axt : forall r s, bemp (rrestrict r s) = true -> ~(exists e, ran r e /\ s e).
Hypothesis bemp_axf : forall r s, bemp (rrestrict r s) = false -> (exists e, ran r e /\ s e).
Parameter is_emp : set Event -> bool.
Hypothesis is_emp_axt : forall r s, is_emp (Intersection _ r s) = true -> ~(exists e, r e /\ s e).
Hypothesis is_emp_axf : forall r s, is_emp (Intersection _ r s) = false -> (exists e, r e /\ s e).

Module AWmm := Wmm A dp.

Definition p2ws (E:Event_struct) (p:Rln Label) : Rln Event :=
  fun w1 => fun w2 => writes E w1 /\ writes E w2 /\ loc w1 = loc w2 /\ 
                      exists l1, exists l2, l1 = f (DW w1) /\ l2 = f (DW w2) /\ p l1 l2.

Definition p2rf E L : Rln Event :=
  fun w => fun r => rfmaps (events E) w r /\ L (f (DR (w,r))).
Definition p2X (E:Event_struct) (p: Rln Label) (L:set Label) : Execution_witness := mkew (p2ws E p) (p2rf E L).

Definition buff_write_step E p L (s:State) (w:Event) : option State :=
  let B := B s in let Rcp := Rcp s in let Rs := Rs s in let Cs := Cs s in
  if is_emp (Intersection Event Rs (fun r' => (A.fences E) w r')) then (*ci0 inter WR*)
  if is_emp (Intersection Event B (fun e => po_iico E w e /\ loc w = loc e)) then (*uniproc CoWW + cc0 inter WW*)
  if is_emp (Intersection Event B (fun e => (A.prop E (p2X E p L)) w e)) then (*propagation*)
        let B' := upd_rs B w in Some (mks B' Rcp Rs Cs)
  else None
  else None
  else None.

Definition flush_write_step E p L (s:State) (w:Event) : option State :=
  let B := B s in let Rcp := Rcp s in let Rs := Rs s in let Cs := Cs s in
  if bin B w then
    if bemp (rrestrict (fun w1 w2 => (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = w) 
         (fun e => udr Rcp e)) 
      then Some (mks B (upd_buff Rcp w) Rs Cs)
    else None
  else None.

Module EPick.
Parameter pick : set Event -> Event.
Axiom pick_singleton :
  forall e, pick (Singleton _ e) = e.
Axiom pick_in :
  forall s, s (pick s).
End EPick.

Definition wbef E B r := EPick.pick (fun w => B w /\ loc r = loc w /\ po_iico E w r /\ 
                                     ~(exists w', loc r = loc w' /\ po_iico E w w' /\ po_iico E w' r)).
Hypothesis wbef_dB : forall E B r, wbef E B r = dB <-> ~(exists w, po_iico E w r /\ loc r = loc w).
Definition waft E B r := EPick.pick (fun w => B w /\ loc r = loc w /\ po_iico E r w /\ 
                                     ~(exists w', loc r = loc w' /\ po_iico E r w' /\ po_iico E w' w)).
Hypothesis waft_dB : forall E B r, waft E B r = dB <-> ~(exists w, po_iico E r w /\ loc r = loc w).

Definition okw E (B:ESet) w r :=
  if bin (fun e => po_loc E e r) w then true
  else if bin B w then true
  else false.
(*Definition rcpw (E:Event_struct) (p:Rln Label) (L:set Label) (s:State) (n:nat) w1 w2
  (f: Event_struct -> Rln Label -> set Label -> Label -> nat -> option State -> option State -> Prop) :=
  writes E w2 /\
  (exists s', exists lst, exists m, le m n /\ (*f is destined to be: machine E p L lst m (Some s) (Some s')*)
   f E p L lst m (Some s) (Some s') /\ Rcp s' w1 w2).*)
Definition FRcp := Event -> Event -> Prop.
Definition buff_read_step E p L (s:State) (w:Event) (r:Event) (f:FRcp) : option State :=
  let B := B s in let Rs := Rs s in let Cs := Cs s in
     if okw E B w r then
     if (is_emp (Intersection _ Rs (fun e => (tc (rel_union (A.ppo E) (A.fences E))) r e))) then (*ii inter RR*)
     if bemp (rrestrict (fun w1 w2 => f w1 w2 /\ w1 = w) (fun e => (rel_seq (A.prop E (p2X E p L)) ((*rc*) (AWmm.hb E (p2X E p L)))) e r)) then (*causality*)
      let Rs' := upd_rs Rs r in Some (mks B (Rcp s) Rs' Cs)
    else None
    else None 
    else None.

Definition visible (E:Event_struct) (*p L*) (s:State) (w:Event) (r:Event) f : bool :=
  let B := B s in
  if is_emp (Intersection _ B (fun e => po_loc E r e)) then (*uniproc CoWR,CoRW1,CoRW2,CoRR*)
         if eqEv_dec (wbef E B r) dB (*if there is no lower bound*)
         then if eqEv_dec (waft E B r) dB (*and there is no upper bound*)
              then if bin (Union _ B (fun e => po_loc E e r /\ e = w)) w (*then w needs to have been committed, or to be in po before r*)
                   then true
                   else false
              else (*if there is an upper bound*)
                   if bin (fun e => (f e (waft E B r) /\ loc r = loc e) \/ (po_loc E e r /\ e = w)) w (*then w must have been prop to the thread of r before the upper bound, or be in po before r*)
                   then true
                   else false
         else (*if there is a lower bound*)
              if bin (fun e => ((e = (wbef E B r) \/ f (wbef E B r) e) /\ loc r = loc e) (*then e is this lower bound or must have been prop to the thread of r after the lower bound*)
                                (*\/ (po_loc E e r /\ ~(exists e', writes E e' /\ loc e' = loc r /\ po_loc E e e' /\ po_loc E e' r) /\ e = w)*)) w 
              then if eqEv_dec (waft E B r) dB 
                   then true
                   else (*and there is an upper bound*) 
                        if bin (fun e => (f e (waft E B r) /\ loc r = loc e) \/ (po_loc E e r /\ e = w)) w (*then w must have been prop to the thread of r before this upper bound, or must be po before r*)
                        then true
                        else false
                   else false
              else false.

Definition flush_resolved_read_step E (*p L*) (s:State) (w:Event) (r:Event) f : option State :=
  let B := B s in let Rcp := Rcp s in let Rs := Rs s in let Cs := Cs s in
  if bin Rs r then
  if is_emp (Intersection _ Rs (fun e => (tc (rel_union (A.ppo E) (A.fences E))) r e)) then (*ci inter RR - here we might want to be more than ppoUfences and actually give ci*)
  if is_emp (Intersection _ B (fun e => (tc (rel_union (A.ppo E) (A.fences E))) r e)) then (*cc inter RW*)
    if visible E (*p L*) s w r f then let Cs' := upd_rs Cs r in Some (mks B Rcp Rs Cs') else None
  else None
  else None
  else None.  

Definition step E p L (s:option State) (l:Label) f : option State :=
  match s with
  | None => None
  | Some s =>
  match l with
  | d de =>
    match de with
    | DW w => buff_write_step E p L s w
    | DR (w,r) => buff_read_step E p L s w r f
    end
  | f de => 
    match de with
    | DW w => flush_write_step E p L s w
    | DR (w,r) => flush_resolved_read_step E (*p L*) s w r f
    end
  end
  end. 

Definition pred (r:Rln Label) (l:Label) :=
  fun l1 => fun l2 => r l1 l2 /\ r l2 l.
Module LPick.
Parameter pick : set Label -> Label.
Axiom pick_singleton :
  forall e, pick (Singleton _ e) = e.
Axiom pick_in :
  forall s, s (pick s).
End LPick.

Module Last.
Parameter last : Rln Label -> Label.
Hypothesis last_in_ran : forall r l, last r = l -> ran r l.
Hypothesis last_is_last : forall r l, last r = l -> ~(exists l', r l l').
Hypothesis no_interv_last :
  forall d p l,
  rel_incl d p ->
  ~(exists l', tc p (last (pred d l)) l' /\ tc p l' l).
Hypothesis before_last_implies_in :
  forall p r l1 l2,
  rel_incl r p ->
  (p l2 (last r) \/ l2 = last r) ->
  p l1 l2 ->
  r l1 l2.
Hypothesis llast :
  forall r l, (~(exists l', r l' l) \/ ran r l) -> ~(exists l', r l l') -> last r = l.
End Last.

Definition evt_of_devt de : Event :=
  match de with
    | DW w => w
    | DR (w,r) => r
  end.

Definition evt_of_label l :=
  match l with 
    | d de | f de => evt_of_devt de 
  end.

Definition devt_of_label l : DEvent :=
  match l with
    | d de | f de => de
  end.

Definition wf_labels (E:Event_struct) (L:set Label) :=
  ((forall w, L (d (DW w)) -> writes E w) /\
   (forall w, L (f (DW w)) -> writes E w)) /\
  ((forall w r, L (d (DR (w,r))) -> rfmaps (events E) w r) /\
   (forall w r, L (f (DR (w,r))) -> rfmaps (events E) w r)) /\
  (forall w, writes E w -> L (f (DW w))) /\
  (forall de, L (f de) -> L (d de)).
  
Parameter EOF : Label.
Hypothesis EOF_bef : 
  forall p (l:Label), p EOF l.

Definition wfi (s: option State) :=
  match s with 
  | None => False
  | Some s => (B s = fun e => False) /\
              (Rs s = fun e => False) /\
              (Rcp s = fun e1 e2 => False)
  end.

Fixpoint machine (E:Event_struct) (r:Rln Label) (L:set Label) (lst:Label) (n:nat) (f:FRcp) {struct n} : Rln (option State) :=
  match n with 
  | O => fun s1 => fun s2 => s1 = s2 /\ Last.last r = EOF /\ wfi s1
  | S m => fun s0 => fun s2 =>
     exists l, exists s1, Last.last r = l /\ 
     machine E (pred r l) L l m f s0 (Some s1) /\ step E r L (Some s1) l f = s2 /\
     wf_ws E (B s1) /\ wf_rs E (Rs s1) /\ wf_buff E (Rcp s1) /\ wf_rs E (Cs s1) 
  end.

Definition machine_not_stuck E p (L:set Label) (f:FRcp) :=
  forall l, L l -> 
  (exists n, exists s0, exists s1, exists s2, wf_ws E (B s1) /\ wf_rs E (Rs s1) /\ wf_rs E (Cs s1) /\ wf_buff E (Rcp s1) /\
     machine E (pred p l) L l n f (Some s0) (Some s1) /\ step E p L (Some s1) l f = Some s2).

Axiom excluded_middle : forall (A:Prop), A \/ ~A.
End Machine.

Module Soundness (A:Archi) (dp:Dp).
  Module AWmm := Wmm A dp.
  Module ABasic := Basic A dp.
  Module AMach := Machine A dp.
  Import AMach.

Lemma wfl_w :
  forall E L,
  wf_labels E L ->
  (forall w, writes E w -> L (f (DW w))).
Proof.
intros E L [? [? [Hle ?]]] w Hw.
  apply Hle; auto.
Qed.

Lemma wfl_e :
  forall E L,
  wf_labels E L ->
  (forall l : Label, L l -> events E (evt_of_label l)).
Proof.
intros E L [[Hwd Hwf] [[Hrd Hrf] ?]] l HL.
case_eq l; intros de Hl; rewrite Hl in HL; case_eq de.

  intros [w r] Hde; rewrite Hde in HL.
    simpl; generalize (Hrd w r HL); intros [? [? ?]]; auto.

  intros w Hde; rewrite Hde in HL.
    simpl; generalize (Hwd w HL); intros [? ?]; auto.

  intros [w r] Hde; rewrite Hde in HL.
    simpl; generalize (Hrf w r HL); intros [? [? ?]]; auto.

  intros w Hde; rewrite Hde in HL.
    simpl; generalize (Hwf w HL); intros [? ?]; auto.
Qed.

Lemma path_ws_wf :
  forall E p (L:set Label),
  (forall w, writes E w -> L (f (DW w))) ->
  linear_strict_order p L ->
  write_serialization_well_formed (events E) (ws (p2X E p L)).
Proof.
intros E p L HLw Hlp; split.    

intros l; split; [|split; [|split]].

  intros ? [e1 [e2 [H12 [? ?]]] | e1 [e2 [H12 [? ?]]]]; auto.

  intros e1 e2 e3 
    [[[Hw1 [Hw2 [Hl12 [l1 [l2 [? [Hl2 H12]]]]]]] [? ?]] 
    [[Hw2' [Hw3 [Hl23 [l2' [l3 [Hl2' [? H23]]]]]]] [? ?]]]; split; [|split]; auto.
  split; [|split]; auto.
  split. 
    rewrite Hl12; auto.
    exists l1; exists l3; split; [|split]; auto.
      destruct_lin Hlp; apply Htrans with (f (DW e2)); split.
        rewrite <- Hl2; auto. rewrite <- Hl2'; auto. 
    
  intros x [[? [? [? [lx [lx' [Hlx [Hlx' Hx]]]]]]] ?].
  rewrite Hlx in Hx; rewrite Hlx' in Hx; destruct_lin Hlp;
  apply Hac with (f (DW x)); auto.

  intros e1 e2 Hd H1 H2. 
  destruct_lin Hlp.
  assert (f (DW e1) <> f (DW e2)) as Hdiff.
    intro Hef; inversion Hef as [Heq]; rewrite Heq in Hd; apply Hd; auto.

  assert (writes E e1) as Hw1.
    destruct H1 as [? [v ?]]; split; auto; exists l; exists v; auto.
  assert (writes E e2) as Hw2.
    destruct H2 as [? [v ?]]; split; auto; exists l; exists v; auto.

  assert (L (f (DW e1))) as Hl1.
    apply HLw; auto.
  assert (L (f (DW e2))) as Hl2.
    apply HLw; auto.
  assert (loc e1 = loc e2) as Heql.
    destruct H1; rewrite ABasic.write_to_implies_this_loc with e1 l; auto;
    destruct H2; apply sym_eq; apply ABasic.write_to_implies_this_loc; auto.
  generalize (Htot (f (DW e1)) (f (DW e2)) Hdiff Hl1 Hl2); intro Hor.

  inversion Hor as [H12 | H21]; [left | right]; split ; auto; split; auto; split; auto; split; auto.
    exists (f (DW e1)); exists (f (DW e2)); split; [|split]; auto.
    exists (f (DW e2)); exists (f (DW e1)); split; [|split]; auto.

  intros e1 e2 [[He1 [l1 [v1 Hw1]]] [[He2 [l2 [v2 Hw2]]] [Heql [lb1 [lb2 [H1 [H2 H12]]]]]]]; 
    exists (loc e1); split; split; auto.
      exists v1; unfold loc; rewrite Hw1; auto.
      exists v2; rewrite Heql; unfold loc; rewrite Hw2; auto.
Qed.

Definition wf_rf_labels E L :=
  (forall r, reads E r -> exists w, rfmaps (events E) w r /\ L (f (DR (w,r)))) /\
  ((forall x w1 w2, L (d (DR (w1, x))) -> L (d (DR (w2, x))) -> w1 = w2) /\
   (forall x w1 w2, L (f (DR (w1, x))) -> L (f (DR (w2, x))) -> w1 = w2)).

Lemma path_rf_wf :
  forall E p L,
  linear_strict_order p L ->
  wf_rf_labels E L ->
  rfmaps_well_formed E (events E) (rf (p2X E p L)).
Proof.
intros E p L Hlin [Hex Huni]; split; [|split].

  intros r Hr; generalize (Hex r Hr); intros [w [Hrfm ?]]; 
  exists w; split; auto.
    destruct Hrfm as [? ?]; auto.
    split; auto.

  intros e1 e2 [? ?]; auto.

  intros r w1 w2 [? ?] [? ?]; subst; auto.
  apply Huni with r; auto; destruct_lin Hlin.
Qed.

Lemma td_tpred :
  forall p lb,
  trans p -> trans (pred p lb).
Proof.
intros p lb Htd x y z [Hxy ?] [Hyz ?]; split; auto.
  apply Htd with y; auto.
Qed.

Lemma upd_rs_keeps :
  forall (R:ESet) r r',
  R r ->
  (upd_rs R r') r.
Proof.
intros q r r' Hin.
unfold upd_rs.
left; auto.
Qed.

Lemma del_rs_keeps :
  forall (Q:ESet) r r',
  r <> r' ->
  Q r ->
  (del_rs Q r') r.
Proof.
intros q r r' Hdiff Hin;
unfold del_rs.
split; auto.
Qed.

Lemma flush_read_same_rs :
  forall E (p:Rln Label) L s0 s1 r wr' r' phi,
  events E r ->
  step E p L (Some s0) (f (DR (wr',r'))) phi = Some s1 ->
  wf_rf_labels E L ->
  (Rs s0) r ->
  (Rs s1) r.   
Proof.
intros E p L s0 s1 r wr' r' phi Her Hs Hwfr Hi.
unfold step in Hs; unfold flush_resolved_read_step in Hs.
destruct (bin (Rs s0) r'); [|inversion Hs];
destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r' e))); [|inversion Hs];
destruct (is_emp (Intersection _ (B s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r' e))); [|inversion Hs].
destruct (visible E (*p L*) s0 wr' r' phi); [|inversion Hs].
  inversion Hs as [Heq]; simpl; auto. 
Qed.

Lemma not_flush_read_step_implies_same_rs :
  forall E (p:Rln Label) L s0 s1 lb r phi,
  events E r ->
  step E p L (Some s0) lb phi = Some s1 ->
  wf_rf_labels E L ->
  (Rs s0) r ->
  (Rs s1) r.  
Proof.
intros E p L s0 s1 lb r phi Her Hs Hwfr Hi; case_eq lb; 
intros de Hlb; rewrite Hlb in Hs; case_eq de; 
intros c Hde; rewrite Hde in Hs; simpl in Hs.

(*d*)

  (*R*)
  destruct c as [w' r']; unfold buff_read_step in Hs.

  destruct (okw E (B s0) w' r'); [|inversion Hs];
  destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r' e))); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w') (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (AWmm.hb E (p2X E p L))) e r'))); 
  inversion Hs; apply upd_rs_keeps; auto.

  (*W*)
  unfold buff_write_step in Hs;
  destruct (is_emp (Intersection Event (Rs s0) (fun r' : Event => (A.fences E) c r'))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s0) (fun e => po_iico E c e /\ loc c = loc e))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s0) (fun e => (A.prop E (p2X E p L)) c e))); [|inversion Hs];
  destruct (is_emp (Intersection _ (Rs s0) (fun r' => loc r' = loc c /\ po_iico E r' c))); [|inversion Hs];
  inversion Hs; auto.

(*f*)
  (*R*)
  destruct c as [w' r']; apply flush_read_same_rs with E p L s0 w' r' phi; auto.

  (*W*)
  unfold flush_write_step in Hs; 
  destruct (bin (B s0) c); [|inversion Hs];
  destruct (bemp (rrestrict (fun w1 w2 : Event => (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\ w1 = c) (fun e : Event => udr (Rcp s0) e))); 
  inversion Hs; auto.
Qed.

Lemma in_order_implies_in_rs :
  forall E (p:Rln Label) L lst n s0 s1 lb wr r phi,
  Included _ (Union _ (dom p) (ran p)) L ->  
  trans p ->
  acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->  
  wf_rf_labels E L ->
  L lb -> 
  p (d (DR (wr,r))) lb -> p (d (DR (wr,r))) lst ->
  (~ (exists l' : Label, tc p lst l' /\ tc p l' lb) \/ lst = lb) ->
  (exists d, trans d /\ rel_incl d (pred p lb) /\ 
     ~(exists l', tc p (Last.last d) l' /\ tc p l' lst) /\
     machine E d L lst n phi (Some s0) (Some s1)) ->
  (Rs s1) r.
Proof.
intros E p L lst n s0 s2 lb'' wr r phi Hudrp Htp Hacp Htotp Hwfr Hllb Hprlb Hprlst Hni Hm.
generalize s2 lst lb'' Hwfr Hm Hllb Hprlb Hprlst Hni; 
clear s2 lst lb'' Hwfr Hm Hllb Hprlb Hprlst Hni; 
induction n; 
intros s2 lst lb'' Hwfr [pd [Htd [Hi [Hniw Hm]]]] Hllb Hprlb Hprlst Hni.
  
  destruct Hm as [? [Heof ?]]; auto.
    assert False as Ht.
      apply Hniw; rewrite Heof; exists (d (DR (wr,r))); split; auto;
      apply trc_step; auto. apply EOF_bef; auto.
    inversion Ht.

  destruct Hm as [lb [s1 [Hdlb [Hm [Hs [? [Hwfq ?]]]]]]];
  fold (machine E (pred pd lb) L lb n phi (Some s0) (Some s1)) in Hm.
  destruct (eqLabel_dec lb (d (DR (wr,r)))) as [Heqlbr | Hneqlbr].
    rewrite Heqlbr in Hs; unfold step in Hs; unfold buff_read_step in Hs.

  destruct (okw E (B s1) wr r); [|inversion Hs];
  destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = wr) 
             (fun e => rel_seq (A.prop E (p2X E pd L)) ((AWmm.hb E (p2X E pd L))) e r))); 
  inversion Hs as [Heqs]; simpl; unfold upd_rs; simpl; right; unfold Ensembles.In; auto.

  assert (exists d, trans d /\ rel_incl d (pred p lb) /\
          ~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lb) /\
          machine E d L lb n phi (Some s0) (Some s1)) as Hex.
    exists (pred pd lb); split; [|split; [|split]]; auto. 
      apply (td_tpred pd lb Htd).
      intros x y [Hxy Hylb]; 
      generalize (Hi x y Hxy); intros [? ?];
      generalize (Hi y lb Hylb); intros [? ?]; split; auto.
      apply Last.no_interv_last; auto. 
        intros x y Hxy; generalize (Hi x y Hxy); intros [? ?]; auto.
  assert (L lb) as Hlb.
    apply Hudrp; auto.
    generalize (Last.last_in_ran pd lb Hdlb); intros [x Hx];
    generalize (Hi x lb Hx); intros [? ?]; right; exists x; auto.
  assert (~ (exists l' : Label, tc p lb l' /\ tc p l' lb) \/ lb = lb) as Hnieq.
    auto.
  assert (p (d (DR (wr,r))) lb) as Hrlb.
    assert (L (d (DR (wr,r)))) as Hlr.
      apply Hudrp; left; exists lb''; auto.
    generalize (Htotp lb (d (DR (wr,r))) Hneqlbr Hlb Hlr); intros [Hlbr | ?]; auto.
    assert (exists l' : Label, tc p (Last.last pd) l' /\ tc p l' lst) as Hc.
      rewrite Hdlb; exists (d (DR (wr,r))); split; apply trc_step; auto.
    contradiction.
  generalize (IHn s1 lb lb Hwfr Hex Hlb Hrlb Hrlb Hnieq); intro Hi1.

  apply (not_flush_read_step_implies_same_rs E pd L s1 s2 lb r phi); auto.
    generalize (Hwfq r Hi1); intros [? ?]; auto. 
Qed.

Lemma upd_buff_keeps :
  forall (B:Buffer) w1 w2 w,
  B w1 w2 ->
 (upd_buff B w) w1 w2.
Proof.
intros b w1 w2 w Hin.
unfold upd_buff;
destruct (bin (udr b) w); auto.
left; auto.
Qed.

Lemma del_buff_keeps :
  forall (B:Buffer) w1 w2 w,
  w1 <> w -> w2 <> w ->
  B w1 w2 ->
  (del_buff B w) w1 w2.
Proof.
intros b w1 w2 w Hd1 Hd2 Hin;
unfold del_buff; auto.
Qed.

Lemma flush_read_same_buff :
  forall E p L s0 s1 w wr r phi,
  step E p L (Some s0) (f (DR (wr,r))) phi = Some s1 ->
  (B s0) w ->
  (B s1) w.  
Proof.
intros E p L s0 s1 w wr' r' phi Hs H12.
unfold step in Hs; unfold flush_resolved_read_step in Hs;
destruct (bin (Rs s0) r'); [|inversion Hs];
destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r' e))); [|inversion Hs];
destruct (is_emp (Intersection _ (B s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r' e))); [|inversion Hs].
destruct (visible E (*p L*) s0 wr' r' phi); [|inversion Hs].
  inversion Hs; auto.
Qed.

Lemma not_flush_write_step_implies_same_buff :
  forall E p L s0 s1 lb w2 phi,
  step E p L (Some s0) lb phi = Some s1 ->
  events E w2 ->
  lb <> d (DW dB) -> lb <> d (DW w2) ->
  (B s0) w2 ->
  (B s1) w2.
Proof.
intros E p L s0 s1 lb w2 phi Hs He2 Hd1 Hd2 H12.
case_eq lb; 
intros de Hlb; rewrite Hlb in Hs; case_eq de; 
intros c Hde; rewrite Hde in Hs; simpl in Hs.

(*d*)

  (*R*)
  destruct c as [w' r']; unfold buff_read_step in Hs.

  destruct (okw E (B s0) w' r'); [|inversion Hs];
  destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r' e))); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w') 
    (fun e => rel_seq (A.prop E (p2X E p L)) ((AWmm.hb E (p2X E p L))) e r'))); 
  inversion Hs; auto.

  (*W*)
  unfold buff_write_step in Hs;
  destruct (is_emp (Intersection Event (Rs s0) (fun r' : Event => (A.fences E) c r'))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s0) (fun e => po_iico E c e /\ loc c = loc e))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s0) (fun e => (A.prop E (p2X E p L)) c e))); [|inversion Hs];
  inversion Hs; apply upd_rs_keeps; auto.

(*f*)

  (*R*)
  rewrite Hde in Hlb; rewrite Hlb in Hd1;
  destruct c as [w' r'];
  apply flush_read_same_buff with E p L s0 w' r' phi; auto.

  (*W*)
  unfold flush_write_step in Hs;
  destruct (bin (B s0) c); [|inversion Hs];
  destruct (bemp (rrestrict (fun w1 w2 : Event => (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\ w1 = c)
              (fun e : Event => udr (Rcp s0) e)));
  inversion Hs; auto.
Qed.

Lemma in_order_implies_in_buff : 
  forall E p L lst n s0 s1 w lb phi,
  wf_labels E L ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->  
  (forall l, L l -> events E (evt_of_label l) ) ->
  (p (d (DW w)) lb) -> 
  (p (d (DW w)) lst) ->
  L (f (DW w)) ->
  (~ (exists l' : Label, tc p lst l' /\ tc p l' lb) \/ lst = lb) ->
  (exists d, trans d /\ rel_incl d (pred p lst) /\ 
     (~(exists l', tc p (Last.last d) l' /\ tc p l' lst) \/ Last.last d = lst) /\
     machine E d L lst n phi (Some s0) (Some s1)) ->
  (B s1) w.
Proof.
intros E p L lst n s0 s2 w lb'' phi Hwfl Hudrp Htp Hacp Htotp Hle 
  Hpwlb'' Hpwlst Hib Hni Hm.
generalize s2 lst lb'' Hpwlb'' Hpwlst Hib Hni Hm; 
clear s2 lst lb'' Hpwlb'' Hpwlst Hib Hni Hm;
induction n; intros s2 lst lb'' Hpwlb'' Hpwlst Hib Hni [pd [Htd [Hi [Hniw Hm]]]].

  destruct Hm as [? [Heof ?]]; auto.
  assert False as Ht.
    inversion Hniw as [Hn | Heq].
      apply Hn; rewrite Heof.
      exists (d (DW w)); split; auto; apply trc_step; auto.
      apply EOF_bef; auto.
      rewrite Heq in Heof; rewrite Heof in Hpwlst.
      generalize (EOF_bef p (d (DW w))); intro Hc; apply Hacp with EOF;
      apply trc_ind with (d (DW w)); apply trc_step; auto.
  inversion Ht.

  destruct Hm as [lb [s1 [Hdlb [Hm [Hs ?]]]]];
  fold (machine E (pred pd lb) L lb n phi (Some s0) (Some s1)) in Hm.
  destruct (eqLabel_dec lb (d (DW w))) as [Heqlbw | Hneqlbw].
    rewrite Heqlbw in Hs; unfold step in Hs; unfold buff_write_step in Hs.
  destruct (is_emp (Intersection Event (Rs s1) (fun r' : Event => (A.fences E) w r'))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s1) (fun e => po_iico E w e /\ loc w = loc e))); [|inversion Hs].
  destruct (is_emp (Intersection _ (B s1) (fun e => (A.prop E (p2X E pd L)) w e))); [|inversion Hs].

    inversion Hs as [Heqs]; simpl. unfold upd_buff.
      (*generalize (udr_dB (B s1) w); intros [Hd Hc]; auto.

      case_eq (bin (udr (B s1)) w); intros Hb.
        generalize (bin_In (udr (B s1)) w Hb). 
          intro Hiw; generalize (Hd Hiw); intros [? ?]; auto. 
        right; split; auto. *) right; unfold Ensembles.In; auto.

  assert (exists d, trans d /\ rel_incl d (pred p lb) /\
          (~(exists l', tc p (Last.last d) l' /\ tc p l' lb) \/ Last.last d = lb) /\
         machine E d L lb n phi (Some s0) (Some s1)) as Hex.
    exists (pred pd lb); split; [|split; [|split]]; auto. 
      apply td_tpred; auto.
        intros x y [Hxy Hylb]; split; auto.
        generalize (Hi x y Hxy); intros [? ?]; auto.
        generalize (Hi y lb Hylb); intros [? ?]; auto.
      left; apply Last.no_interv_last; auto.
        intros x y Hxy; generalize (Hi x y Hxy); intros [? ?]; auto. 

  assert (L lb) as Hllb.
    generalize (Last.last_in_ran pd lb Hdlb); intros [x Hx]; generalize (Hi x lb Hx); intros [? ?].
    apply Hudrp; left; exists lst; auto.

  assert (~ (exists l' : Label, tc p lb l' /\ tc p l' lb) \/ lb = lb) as Hnilb.
    auto.
  assert (p (d (DW w)) lb) as Hpdwlb.
    assert (L (d (DW w))) as Hlw.
      apply Hudrp; left; exists lb''; auto.
    generalize (Htotp lb (d (DW w)) Hneqlbw Hllb Hlw); intros [Hlbw | ?]; auto.
    inversion Hniw as [Hniwp | Heqlst].
      Focus 2.
      generalize (Last.last_in_ran pd lst Heqlst); intros [x Hx].
      generalize (Hi x lst Hx); intros [? ?].
      assert (tc p lst lst) as Hc.
        apply trc_step; auto.
      generalize (Hacp lst Hc); intro Ht.
      inversion Ht.

    assert (exists l' : Label, tc p (Last.last pd) l' /\ tc p l' lst) as Hc.
      rewrite Hdlb; exists (d (DW w)); split; apply trc_step; auto.
    contradiction.    
  assert (lb <> (d (DW w))) as Hdiff.
    auto.

  generalize (IHn s1 lb lb Hpdwlb Hpdwlb Hib Hnilb Hex); intros His1.

   assert (ran pd lb) as Hran.
     destruct Hdlb as [? ?]; apply Last.last_in_ran; auto.

  apply not_flush_write_step_implies_same_buff with E pd L s1 lb phi; auto.
      assert (w = evt_of_label (d (DW w))) as Heq.
      simpl; auto. rewrite Heq; apply Hle; auto.
      apply Hudrp; left; exists lb; auto.

   assert (L lb) as Helb.
      apply Hudrp; right. 
        destruct Hran as [lb' Hran].
        generalize (Hi lb' lb Hran); intros [? ?]; exists lb'; auto.

        intro Heq; rewrite Heq in Helb. 
        generalize (Hle (d (DW dB)) Helb); simpl; intro.

            assert (dB = dB) as Ht.
              trivial.
            generalize Ht; fold (dB <> dB). 
            apply dB_not_in_E with E; auto.   
Qed.

(*Definition wf_l_p E p (L:set Label) :=
  forall l, L l ->
  ~(exists s1, exists s2, exists s1', exists s2', s1 <> s1' /\ 
    step E p L (Some s1) l = s2 /\ step E p L (Some s1') l = s2').  *)

(*Lemma mns_implies_not_none :
  forall E p (L:set Label) s l, 
  L l ->
  (*wf_l_p E p L ->*)
  machine_not_stuck E p L ->
  ~(step E p L (Some s) l = None).
Proof.
intros E p L s l Hd (*Hus*) Hmns Hn.
destruct (Hmns l Hd) as [n [s0 [s1 [s2 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]]; auto.
generalize (excluded_middle (s = s1)); intros [Heqs | Hneqs].
  rewrite Heqs in Hn; rewrite Hn in Hs; inversion Hs.
  generalize (Hus l Hd); intro.
  assert (exists s1, exists s2, exists s1', exists s2', s1 <> s1' /\ 
    step E p L (Some s1) l = s2 /\ step E p L (Some s1') l = s2') as Hc.
    exists s1; exists (Some s2); exists s; exists None; split; [|split]; auto.
  contradiction.
Qed.

Lemma mns_up_to_l_implies_not_none :
  forall E p (L:set Label) s l n s0 s1 s2, 
  L l ->
  wf_l_p E p L ->
  machine E (pred p l) L l n (Some s0) (Some s1) ->
  step E p L (Some s1) l = Some s2 ->
  ~(step E p L (Some s) l = None).
Proof.
intros E p L s l n s0 s1 s2 Hd Hus Hmns Hs Hn.
generalize (excluded_middle (s = s1)); intros [Heqs | Hneqs].
  rewrite Heqs in Hn; rewrite Hn in Hs; inversion Hs.
  generalize (Hus l Hd); intro.
  assert (exists s1, exists s2, exists s1', exists s2', s1 <> s1' /\ 
    step E p L (Some s1) l = s2 /\ step E p L (Some s1') l = s2') as Hc.
    exists s1; exists (Some s2); exists s; exists None; split; [|split]; auto.
  contradiction.
Qed.*)

Lemma wdl_w :
  forall E L,
  wf_labels E L ->
  (forall w, writes E w -> L (d (DW w))).
Proof.
intros E L [? [? [Hle Hfd]]] w Hw.
  apply Hfd; apply Hle; auto.
Qed.

Lemma rs_step :
  forall E p L s0 s1 l e phi,
  ~Rs s0 e ->
  Rs s1 e ->
  step E p L (Some s0) l phi = Some s1 ->
  (exists w, l = d (DR (w,e))).
Proof.
intros E p L s0 s1 l e phi Hnr Hr Hs.
case_eq l; intros de Hl; rewrite Hl in Hs; clear Hl; case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde; exists w; auto.
  unfold step in Hs; unfold buff_read_step in Hs.
  destruct (okw E (B s0) w r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (bemp
             (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w)
                (fun e : Event =>
                 rel_seq (A.prop E (p2X E p L)) (AWmm.hb E (p2X E p L)) e r))); [|inversion Hs].
  inversion Hs as [Heq]; rewrite <- Heq in Hr; simpl in Hr; unfold upd_rs in Hr.
    inversion Hr as [Hc | e' Heqr]; [contradiction|rewrite Heqr]; auto.
 
  intros w Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_write_step in Hs;
  destruct (is_emp
           (Intersection Event (Rs s0) (fun r' : Event => A.fences E w r'))); [|inversion Hs];
  destruct (is_emp
            (Intersection _ (B s0)
               (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s0) (fun e : Event => A.prop E (p2X E p L) w e))); [|inversion Hs];
  inversion Hs as [Heq]; rewrite <- Heq in Hr; simpl in Hr; contradiction.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold flush_resolved_read_step in Hs.
  destruct (bin (Rs s0) r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (is_emp
             (Intersection Event (B s0)
                (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (visible E (*p L*) s0 w r phi); [|inversion Hs].
  inversion Hs as [Heq]; rewrite <- Heq in Hr; simpl in Hr; contradiction.

  intros w Hde; rewrite Hde in Hs; clear Hde; unfold step in Hs; 
  unfold flush_write_step in Hs.

  destruct (bin (B s0) w); [|inversion Hs];
  destruct (bemp
            (rrestrict
               (fun w1 w2 : Event =>
                (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
                w1 = w) (fun e : Event => udr (Rcp s0) e))); [|inversion Hs].
      inversion Hs as [Heq]; rewrite <- Heq in Hr; simpl in Hr; contradiction.
Qed.  

Lemma in_rs_implies_d_before :
  forall E p L lst n s0 s1 dr r phi,
  wf_labels E L ->
  wf_rf_labels E L ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p ->
  events E r ->
  evt_of_devt dr = r ->
  wf_rs E (Rs s1) ->
  L (d dr) ->
  (Rs s1) r ->
  (exists d, trans d /\ rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
  p (d dr) lst.
Proof.
intros E p L lst n s0 s1 dr r phi Hwfl Hwfrfl Hudr Htp Her Hdr Hwfrs Hinldr Hr Hex.
generalize p lst s1 Hwfrs Hudr Htp Hr Hex; clear p lst s1 Hwfrs Hudr Htp Hr Hex;
induction n; intros p lst s1 Hwfrs Hudr Htp Hr Hex.

Focus 2.

  destruct Hex as [rln [Htdr [Hi [Hniw Hm]]]].
  destruct Hm as [l [s [Hl [Hm [Hs [? [Hwfrss ?]]]]]]];
  fold (machine E (pred rln l) L l n phi (Some s0) (Some s)) in Hm.
  assert (p l lst) as Hpllst.
    generalize (Last.last_in_ran rln l Hl); intros [x' Hx].
    generalize (Hi x' l Hx); intros [? ?]; auto.

  generalize (excluded_middle (Rs s r)); intros [Hrs | Hnrs].
    apply Htp with l; auto.
    assert (exists d, trans d /\ rel_incl d (pred rln l) /\
      (~ (exists l' : Label, tc rln (Last.last d) l' /\ tc rln l' l) \/
      Last.last d = l) /\ machine E d L l n phi (Some s0) (Some s)) as Hex.
      exists (pred rln l); split; [|split; [|split]]; auto.
        apply td_tpred; auto. 
        intros x y Hxy; auto.
        left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

    assert (Included Label (Union Label (dom rln) (ran rln)) L) as Hudrrln.
      intros x Hx; apply Hudr; inversion Hx as [e [y Hdom] | e [y Hran]].
        generalize (Hi x y Hdom); intros [? ?]; left; exists y; auto.
        generalize (Hi y x Hran); intros [? ?]; right; exists y; auto.

    generalize (IHn rln l s Hwfrss Hudrrln Htdr Hrs Hex).
    intros Hrln; generalize (Hi (d dr) l Hrln); intros [? ?]; auto. 
    generalize (rs_step E rln L s s1 l r phi Hnrs Hr Hs);
    intros [w Heql].

    case_eq dr.
   
    intros [w' r'] Hisdr; rewrite Hisdr in Hdr.
    inversion Hdr as [Heqrr']; simpl in Heqrr'; rewrite Heqrr'.
    destruct Hwfrfl as [? [Heqd ?]]; rewrite Heqd with r w' w; auto.
      rewrite <- Heql; auto.
      rewrite <- Heqrr'; rewrite Hisdr in Hinldr; auto.
      apply Hudr; left; exists lst; rewrite <- Heql; auto.

    intros e Hisdw; rewrite Hisdw in Hinldr.
    destruct Hwfl as [[Hdww ?] ?]; generalize (Hdww e Hinldr); intros [? [? [? Hwe]]].
    generalize (Hwfrs r Hr); intros [? [? [? Hrr]]].
    rewrite Hisdw in Hdr; inversion Hdr as [Heqre]; simpl in Heqre;
    rewrite Heqre in Hwe; rewrite Hwe in Hrr; inversion Hrr.

destruct Hex as [rln [Htdr [Hi [Hniw Hm]]]].
  destruct Hm as [Heqs [? [? [Hwfrsi ?]]]]; auto. 
  inversion Heqs as [Heq]; rewrite <- Heq in Hr.
  rewrite Hwfrsi in Hr; inversion Hr.
Qed. 

Lemma okw_ext :
  forall E B w r,
  well_formed_event_structure E ->
  okw E B w r = true ->
  po_loc E w r \/ B w.
Proof.
intros E B w r Hwf Hok.
unfold okw in Hok.
case_eq (bin (fun e => po_loc E e r) w); intro Hpo; auto; rewrite Hpo in Hok.
  generalize (bin_In (fun e : Event => po_loc E e r) w Hpo); intros Hpowr; auto. 

case_eq (bin B w); intros Hb; auto; rewrite Hb in Hok.
  right; apply bin_In; auto.
  inversion Hok.
Qed.

Lemma okwf_ext :
  forall E B w r,
  well_formed_event_structure E ->
  okw E B w r = false ->
  ~po_loc E w r /\ ~B w.
Proof.
intros E B w r Hwf Hok.
unfold okw in Hok.
case_eq (bin (fun e => po_loc E e r) w); intro Hpo; auto; rewrite Hpo in Hok.
  inversion Hok.

case_eq (bin B w); intros Hb; auto; rewrite Hb in Hok.
  inversion Hok.
  generalize (nbin_nIn (fun e : Event => po_loc E e r) w Hpo); intro.
  split; auto; apply nbin_nIn; auto.
Qed.

Lemma okwf_stable :
  forall E p L s1 s2 l w r phi,
  well_formed_event_structure E ->
  step E p L (Some s1) l phi = Some s2 ->
  okw E (B s2) w r = false ->
  okw E (B s1) w r = false.
Proof.
intros E p L s1 s2 l w r phi Hwf Hs Hokf.
case_eq l; intros de Hl; rewrite Hl in Hs; clear Hl; case_eq de.

  intros [wr rr] Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_read_step in Hs.
    destruct (okw E (B s1) wr rr); [|inversion Hs];
    destruct (is_emp
            (Intersection Event (Rs s1)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) rr e))); [|inversion Hs];
    destruct (bemp
             (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = wr)
                (fun e : Event =>
                 rel_seq (A.prop E (p2X E p L)) (AWmm.hb E (p2X E p L)) e rr))); [|inversion Hs].
    inversion Hs as [Heq]; rewrite <- Heq in Hokf; simpl in Hokf; auto.

  intros ww Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_write_step in Hs.
    destruct (is_emp
           (Intersection Event (Rs s1) (fun r' : Event => A.fences E ww r'))); [|inversion Hs];
    destruct (is_emp
            (Intersection _ (B s1)
               (fun e : Event => po_iico E ww e /\ loc ww = loc e))); [|inversion Hs].
    destruct (is_emp
             (Intersection _ (B s1) (fun e : Event => A.prop E (p2X E p L) ww e))); [|inversion Hs].
    inversion Hs as [Heq]; rewrite <- Heq in Hokf; simpl in Hokf; auto.
      unfold upd_rs in Hokf.
(*      case_eq (bin (udr (B s1)) ww); intro Hi; rewrite Hi in Hokf; auto.*)
      case_eq (okw E (B s1) w r); intro Hok; auto.
      generalize (okw_ext E (B s1) w r Hwf Hok); intro Hor.
      generalize (okwf_ext E (Union _ (B s1)
            (fun e : Event => e = ww)) w r Hwf Hokf);
      intros [Hnpo Hnb].
        inversion Hor as [Hpo | Hudr].
          contradiction.
          assert False as Ht.
            apply Hnb.
            (*destruct Hudr as [e' [e Hew] | e' [e Hew]].
               left; exists e; left; auto.
               right; exists e; left; auto.*) left; auto.
          inversion Ht.

  intros [wr rr] Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold flush_resolved_read_step in Hs.
  destruct (bin (Rs s1) rr); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s1)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) rr e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s1)
                (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) rr e))); [|inversion Hs].
  destruct (visible E (*p L*) s1 wr rr phi); [|inversion Hs].
  inversion Hs as [Heq]; rewrite <- Heq in Hokf; simpl in Hokf; auto.

  intros ww Hde; rewrite Hde in Hs; clear Hde; unfold step in Hs;
  unfold flush_write_step in Hs.
  destruct (bin (B s1) ww); [|inversion Hs].  
  destruct (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = ww)
              (fun e : Event => udr (Rcp s1) e))); [|inversion Hs].
  inversion Hs as [Heq]; rewrite <- Heq in Hokf; simpl in Hokf; auto.
Qed.

Lemma same_state :
  forall E p L n s0 s1 s2 l phi,
  trans p ->
  machine E (pred p l) L l n phi (Some s0) (Some s1) ->
  machine E (pred p l) L l n phi (Some s0) (Some s2) ->
  s1 = s2.
Proof.
intros E p L n s0 s1 s2 l phi Htp Hm1 Hm2.
generalize l s1 s2 Hm1 Hm2; clear l s1 s2 Hm1 Hm2;
induction n; intros l s1 s2 Hm1 Hm2.
  destruct Hm1 as [Hse01 ?]; destruct Hm2 as [Hse02]; 
  inversion Hse01 as [He01]; inversion Hse02 as [He02];
  rewrite <- He01; auto.

  destruct Hm1 as [l1 [s'1 [Hl1 [Hm1 [Hs1 ?]]]]];
  fold (machine E (pred (pred p l) l1) L l1 n phi (Some s0) (Some s'1)) in Hm1;
  destruct Hm2 as [l2 [s'2 [Hl2 [Hm2 [Hs2 ?]]]]];
  fold (machine E (pred (pred p l) l2) L l2 n phi (Some s0) (Some s'2)) in Hm2;
  rewrite <- Hl2 in Hm2; rewrite Hl1 in Hm2.

  generalize (Last.last_in_ran (pred p l) l1 Hl1); intros [e [Hel1 Hl1l]].
  assert (pred p l1 = pred (pred p l) l1) as Heq.
    apply ext_rel; intros x y; split; intros [Hxy Hyl]; split; auto.
      split; auto.
        apply Htp with l1; auto.
      split; auto.
      destruct Hxy as [? ?]; auto.
      destruct Hyl as [? ?]; auto.

  rewrite <- Heq in Hm1; rewrite <- Heq in Hm2.
  generalize (IHn l1 s'1 s'2 Hm1 Hm2); intro He';
  rewrite <- Hl1 in Hs1; rewrite Hl2 in Hs1; 
  rewrite He' in Hs1; rewrite Hs1 in Hs2; inversion Hs2; auto.
Qed.

Hypothesis mach_det :
  forall E p L l m n s0 s0' s1 s2 phi,
  machine E (pred p l) L l m phi (Some s0) (Some s1) ->
  machine E (pred p l) L l n phi (Some s0') (Some s2) ->
  s0 = s0' /\ m = n.

Lemma okw_stable :
  forall E (p:Rln Label) (L:set Label) n m s0 s0' s1 s2 l1 l2 w r phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p ->
  acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->  
  p l1 l2 ->
  machine E (pred p l1) L l1 m phi (Some s0) (Some s1) ->
  (exists d : Rln Label,
  (trans d /\ rel_incl d (pred p l2) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' l2) \/
        Last.last d = l2) /\ machine E d L l2 n phi (Some s0') (Some s2))) ->
  okw E (B s1) w r = true ->
  okw E (B s2) w r = false ->
  False.
Proof.
intros E p L n m s0 s0' s1 s2 l1 l2 w r phi Hwf Hudr Htp Hacp Htot H12 Hm Hexd Hokt Hokf.
generalize l2 s2 H12 Hokf Hexd; clear l2 s2 H12 Hokf Hexd; induction n;
intros l2 s3 H12 Hokf Hexd.
Focus 2.
destruct Hexd as [rln [Htr [Hi [Hlast Hm']]]];
destruct Hm' as [l [s2 [Hl [Hm' [Hs ?]]]]];
fold (machine E (pred rln l) L l n phi (Some s0') (Some s2)) in Hm';
destruct (eqLabel_dec l1 l) as [Heq | Hneq].

rewrite Heq in Hm.
assert (rel_incl rln p) as Hincl.
  intros x y Hxy; generalize (Hi x y Hxy); intros [? ?]; auto.
assert (pred rln l = pred p l) as Heqr.
  apply ext_rel; intros x y; split; intros [Hxy Hyl]; split.
  generalize (Hi x y Hxy); intros [? ?]; auto.
  generalize (Hi y l Hyl); intros [? ?]; auto.
  assert (p y (Last.last rln) \/ y = (Last.last rln)) as Horyl.
    left; rewrite Hl; auto.
  generalize (Last.before_last_implies_in p rln x y Hincl Horyl Hxy);
  intro Hrxy; auto.
  assert (p (Last.last rln) (Last.last rln) \/ (Last.last rln) = (Last.last rln)) as Horyl.
    right; auto.
  rewrite <- Hl in Hyl; rewrite <- Hl;
  generalize (Last.before_last_implies_in p rln y (Last.last rln) Hincl Horyl Hyl);
  intro Hryl; auto.
rewrite Heqr in Hm'.
assert (s0 = s0' /\ m = n) as Hdet.
  apply mach_det with E p L l s1 s2 phi; auto.   
destruct Hdet as [Heq00' Heqnm];
rewrite Heq00' in Hm;
rewrite Heqnm in Hm.
assert (s1 = s2) as Heqs.
  apply same_state with E p L n s0' l phi; auto.

rewrite <- Heqs in Hs;
generalize (okwf_stable E rln L s1 s3 l w r phi Hwf Hs Hokf);
intro Hc; rewrite Hc in Hokt; inversion Hokt. 

apply IHn with l s2; auto.
rewrite <- Hl.
  inversion Hlast as [Hni | Heq]; clear Hlast.
    assert (L l) as HLl.
      generalize (Last.last_in_ran rln l Hl); intros [e Hrln].
      generalize (Hi e l Hrln); intros [Hip ?].
      apply Hudr; right; exists e; auto.
    assert (L l1) as HLl1.
      apply Hudr; left; exists l2; auto.
    rewrite Hl; generalize (Htot l1 l Hneq HLl1 HLl); intros [|H1l]; auto.
    assert False as Ht.
      apply Hni; rewrite Hl; exists l1; split; apply trc_step; auto.
    inversion Ht.
    rewrite Heq; auto.  

  apply okwf_stable with rln L s3 l phi; auto.

  exists (pred rln l); split; [|split; [|split]]; auto.
   apply td_tpred; auto.
   intros x y [Hxy ?]; split; auto.
     generalize (Hi x y Hxy); intros [? ?]; auto; split; auto. 
     generalize (Hi y l H0); intros [? ?]; auto; split; auto.
   left; apply Last.no_interv_last; auto.
     intros x y Hxy; generalize (Hi x y Hxy); intros [? ?]; auto. 

destruct Hexd as [rln [Htrans [Hi [Hor Hm']]]];
inversion Hm' as [Heqs [Heof ?]];
rewrite Heof in Hor.
inversion Hor as [Hni|Heq]; clear Hor.
  apply Hni; exists l1; split; apply trc_step; auto.
  apply EOF_bef; auto.
  rewrite <- Heq in H12.
  generalize (EOF_bef p l1); intro He1.
  assert (tc p EOF EOF) as Hc.
    apply trc_ind with l1; apply trc_step; auto.
  apply (Hacp EOF Hc).
Qed.

Lemma in_rs_implies_okw :
  forall E L p n s0 s1 lst w r phi,
  well_formed_event_structure E ->
  wf_labels E L ->
  wf_rf_labels E L ->
  Included _ (Union _ (dom p) (ran p)) L ->
  acyclic p ->
  trans p ->
  (forall l1 l2 : Label, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->
  wf_rs E (Rs s1) ->
  (exists d, trans d /\ rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
  machine_not_stuck E p L phi ->  
  rf (p2X E p L) w r ->
  bin (Rs s1) r = true ->
  okw E (B s1) w r = true.
Proof.
intros E L p n s0 s1 lst w r phi Hwf Hwfl Hwfrfl Hudr Hacp Htp Htotp Hwfrs Hm Hmns Hrf Hi.
case_eq (okw E (B s1) w r); intro Hok; auto.
generalize (bin_In (Rs s1) r Hi); clear Hi; intro Hi.
assert (events E r) as Her.
  generalize (Hwfrs r Hi); intros [? ?]; auto.
assert (evt_of_devt (DR (w, r)) = r) as Hdr.
  simpl; auto.
generalize Hwfl; intros Hwfl'; destruct Hrf as [? Hlf]; destruct Hwfl' as [? [? [? Hdf]]]; generalize (Hdf (DR (w,r)) Hlf); intro Hld.
generalize (in_rs_implies_d_before E p L lst n s0 s1 (DR (w,r)) r phi Hwfl Hwfrfl Hudr Htp Her Hdr Hwfrs Hld Hi Hm);
intro Hp.
generalize (Hmns (d (DR (w,r))) Hld);
intros [m [s [s' [s'' [Hwfb [Hwfrs' [Hwfrcp [Hwfrc [Hm' Hs']]]]]]]]].
simpl in Hs'; unfold buff_read_step in Hs'.
case_eq (okw E (B s') w r); intro Hok'; rewrite Hok' in Hs'; [|inversion Hs'].
assert False as Ht.
  apply okw_stable with E p L n m s s0 s' s1 (d (DR (w,r))) lst w r phi; auto.
  
inversion Ht.
Qed. 

Lemma path_unirf : 
  forall E p L e1 e2 phi,
  well_formed_event_structure E ->
  wf_labels E L ->
  (*wf_l_p E p L ->*)
  wf_rf_labels E L ->
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->  
  po_loc_llh E e1 e2 -> ~ rf (p2X E p L) e2 e1.
Proof.
intros E p L e1 e2 phi Hwf Hwfl (*Hwflp*) Hwfrfl Hlp Hmns H12 Hrf'.
assert (trans p) as Htp.
  destruct_lin Hlp.
  intros x1 x2 x3 H1 H2; apply (Htrans x1 x2 x3); split; auto.
assert (acyclic p) as Hacp.
  destruct_lin Hlp.
  intros x Hx; apply Hac with x; rewrite trans_tc in Hx; auto.
assert (L (f (DR (e2,e1)))) as Hdl.
  simpl in Hrf'; unfold p2rf in Hrf'; destruct Hrf'; auto.
destruct (Hmns (f (DR (e2,e1))) Hdl) as [n [s0 [s1 [s2 (*[Hwfm*) [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
simpl in Hs; unfold flush_resolved_read_step in Hs.

case_eq (bin (Rs s1) e1); intro Hiq; rewrite Hiq in Hs; [| inversion Hs].
assert ((exists d : Rln Label,
    trans d /\
    rel_incl d (pred p (f (DR (e2, e1)))) /\
    (~
     (exists l' : Label, tc p (Last.last d) l' /\ tc p l' (f (DR (e2, e1)))) \/
     Last.last d = f (DR (e2, e1))) /\
    machine E d L (f (DR (e2, e1))) n phi (Some s0) (Some s1))) as Hex.
  exists (pred p (f (DR (e2,e1)))); split; [|split; [|split]]; auto.
    apply td_tpred; auto. intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.
destruct_lin Hlp.
generalize (in_rs_implies_okw E L p n s0 s1 (f (DR (e2,e1))) e2 e1 phi Hwf Hwfl Hwfrfl Hdr Hacp Htp Htot Hwfq Hex Hmns Hrf' Hiq);
intro Hok; generalize (okw_ext E (B s1) e2 e1 Hwf Hok); intros [Hpo21 | Hb].
  assert (po_iico E e1 e1) as Hpo11.
    destruct H12 as [? [? ?]]; destruct Hpo21 as [? ?];
    apply ABasic.po_trans with e2; auto.
  assert False as Ht.
    generalize Hpo11; apply ABasic.po_ac; auto.
  inversion Ht.
  
  destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) e1 e))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) e1 e))); [|inversion Hs].

  unfold visible in Hs.
  case_eq (is_emp (Intersection _ (B s1) (fun e : Event => po_loc E e1 e))); intro Hemp; rewrite Hemp in Hs; [|inversion Hs].
    apply (is_emp_axt (B s1) (fun e : Event => po_loc E e1 e) Hemp); exists e2; split; auto.
      destruct H12 as [? [? ?]]; split; auto.
Qed.

Lemma pred_incl :
  forall r l,
  rel_incl (pred r l) r.
Proof.
intros r l x y [Hxy ?]; auto.
Qed.

Lemma pred_incl2 :
  forall r1 r2 l,
  rel_incl r1 r2 ->
  rel_incl (pred r1 l) (pred r2 l).
Proof.
intros r1 r2 l Hi12 x y [Hxy Hor]; split; auto.
Qed.

Lemma rcp_swap_contrad :
  forall E p L l s s1 w w' phi,
  wf_buff E (Rcp s) ->
  step E p L (Some s) l phi = Some s1 ->
  loc w = loc w' ->
  Rcp s w w' -> Rcp s1 w' w ->
  False.
Proof.
intros E p L l s s1 w w' phi Hwfb Hs Heql Hbs Hb1.
case_eq l; intros de Hl; rewrite Hl in Hs; clear Hl; case_eq de.

  intros [wr r] Hde;
    rewrite Hde in Hs; clear Hde; simpl in Hs; unfold buff_read_step in Hs.

    destruct (okw E (B s) wr r); [|inversion Hs];
    destruct (is_emp (Intersection Event (Rs s) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
    destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = wr) 
      (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (AWmm.hb E (p2X E p L))) e r))); [|inversion Hs].

    inversion Hs as [Heqs]; rewrite <- Heqs in Hb1; simpl in Hb1.
    destruct Hwfb as [? [? [Hac ?]]].
    assert (tc (rrestrict (Rcp s) (fun e => loc e = loc w)) w w) as Hc.
      apply trc_ind with w'; apply trc_step; split; unfold Ensembles.In; auto.
    apply (Hac w w Hc).

  intros wr Hde;
    rewrite Hde in Hs; clear Hde; simpl in Hs; unfold buff_write_step in Hs.
      destruct (is_emp (Intersection Event (Rs s) (fun r' : Event => (A.fences E) wr r'))); [|inversion Hs];
      destruct (is_emp (Intersection _ (B s) (fun e => po_iico E wr e /\ loc wr = loc e))); [|inversion Hs].
      destruct (is_emp (Intersection _ (B s) (fun e => (A.prop E (p2X E p L)) wr e))); [|inversion Hs].
    inversion Hs as [Heqs];
    rewrite <- Heqs in Hb1; simpl in Hb1.
    destruct Hwfb as [? [? [Hac ?]]].
    assert (tc (rrestrict (Rcp s) (fun e => loc e = loc w)) w w) as Hc.
      apply trc_ind with w'; apply trc_step; split; unfold Ensembles.In; auto.
    apply (Hac w w Hc).

  intros [wr r] Hde;
    rewrite Hde in Hs; clear Hde; simpl in Hs; unfold flush_resolved_read_step in Hs;
    inversion Hs as [Heqs].
      destruct (bin (Rs s) r); [|inversion Heqs].
      destruct (is_emp (Intersection Event (Rs s) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
      destruct (is_emp (Intersection _ (B s) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
      destruct (visible E (*p L*) s wr r phi) in Hs; [|inversion Hs].
      inversion Hs as [Heq]; rewrite <- Heq in Hb1; simpl in Hb1.
         destruct Hwfb as [? [? [Hac ?]]].
         assert (tc (rrestrict (Rcp s) (fun e => loc e = loc w)) w w) as Hc.
           apply trc_ind with w'; apply trc_step; split; unfold Ensembles.In; auto.
         apply (Hac w w Hc). 

  intros wr Hde;
    rewrite Hde in Hs; clear Hde; simpl in Hs; unfold flush_write_step in Hs.
    destruct (bin (B s) wr); [|inversion Hs].
    destruct (bemp (rrestrict (fun w1 w2 : Event => (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\ w1 = wr)
              (fun e : Event => udr (Rcp s) e))); inversion Hs.

    destruct Hwfb as [? [? [Hac ?]]].
    assert (tc (rrestrict (Rcp s) (fun e => loc e = loc w)) w w) as Hc.
      apply trc_ind with w'; apply trc_step; split; unfold Ensembles.In; auto.
      inversion Hs as [Heqs]; rewrite <- Heqs in Hb1; auto.
    unfold upd_buff in Hb1. case_eq (bin (udr (Rcp s)) wr); intro His; 
    rewrite His in Hb1.
    assert (tc (rrestrict (Rcp s) (fun e => loc e = loc w)) w w) as Hc.
      apply trc_ind with w'; apply trc_step; split; unfold Ensembles.In; auto.
      simpl in Hb1; auto. 
      simpl in Hb1.
      inversion Hb1 as [|[Hor Heq]]; clear Hb1.
      assert (tc (rrestrict (Rcp s) (fun e => loc e = loc w)) w w) as Hc.
        apply trc_ind with w'; apply trc_step; split; unfold Ensembles.In; auto.
      assert False as Ht.
        apply (Hac w w Hc).
      inversion Ht.
        rewrite <- Heq in His.
        assert (bin (udr (Rcp s)) w = true) as Hi.
           apply In_bin; left; exists w'; auto.
        rewrite Hi in His; inversion His.

    apply (Hac w w Hc).
Qed.

Lemma rcp_swap_contrad' :
  forall E p L s s1 w w' phi, 
  step E p L (Some s) (f (DW w)) phi = Some s1 ->
  ~udr (Rcp s) w -> Rcp s1 w w' -> w <> w' ->
  False.
Proof.
intros E p L s s1 w w' phi Hs Hns Hs1 Hneq.
simpl in Hs; unfold flush_write_step in Hs.
destruct (bin (B s) w); [|inversion Hs].
destruct (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = w)
              (fun e : Event => udr (Rcp s) e))); [|inversion Hs].
inversion Hs as [Heqs]; 
rewrite <- Heqs in Hs1; clear Heqs;
simpl in Hs1; unfold upd_buff in Hs1.
destruct (bin (udr (Rcp s)) w).
  apply Hns; left; exists w'; auto.
  inversion Hs1 as [|[? Heq]].
    apply Hns; left; exists w'; auto.
    apply Hneq; auto.
Qed.

Lemma flush_read_b_step :
  forall E p L s0 s1 w wr r phi,
  ~((B s0) w) -> ((B s1) w) ->
  step E p L (Some s0) (f (DR (wr,r))) phi = Some s1 ->
  f (DR (wr,r)) = d (DW w).
Proof.
intros E p L s0 s1 w' w r phi Hni0 Hi1 Hs.
unfold step in Hs; unfold flush_resolved_read_step in Hs.
destruct (bin (Rs s0) r); [|inversion Hs];
destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
destruct (is_emp (Intersection _ (B s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
destruct (visible E (*p L*) s0 w r phi); [|inversion Hs].
      inversion Hs as [Heq]; rewrite <- Heq in Hi1; simpl in Hi1; contradiction. 
Qed.

Lemma b_step :
  forall E p L s0 s1 lb w phi,
  events E w ->
  ~((B s0) w) -> ((B s1) w) ->
  step E p L (Some s0) lb phi = Some s1 ->
  lb = d (DW w).
Proof.
intros E p L s0 s1 lb w' phi Hew' Hni0 Hi1 Hs.
case_eq lb; intros de Hde; rewrite Hde in Hs; case_eq de.

  (*Buff*)
    (*R*)
    intros [w r] Hr; rewrite Hr in Hs; unfold step in Hs; unfold buff_read_step in Hs. 

    destruct (okw E (B s0) w r); [|inversion Hs];
    destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
    destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (AWmm.hb E (p2X E p L))) e r))); 
      inversion Hs as [Heq]; rewrite <- Heq in Hi1; simpl in Hi1; contradiction.


    (*W*)
    intros w Hw; rewrite Hw in Hs; unfold step in Hs; unfold buff_write_step in Hs.
      destruct (is_emp (Intersection Event (Rs s0) (fun r' : Event => (A.fences E) w r'))); [|inversion Hs];
      destruct (is_emp (Intersection _ (B s0) (fun e => po_iico E w e /\ loc w = loc e))); [|inversion Hs].
      destruct (is_emp (Intersection _ (B s0) (fun e => (A.prop E (p2X E p L)) w e))); [|inversion Hs].
      inversion Hs as [Heq]; rewrite <- Heq in Hi1; simpl in Hi1.
      destruct Hi1 as [? Hi1 | ? Hi1]; unfold upd_buff in Hi1; destruct (bin (B s0) w).
        assert ((B s0) x) as Hc.
          auto.
        contradiction.

        assert ((B s0) x) as Hc.
          auto.
        contradiction.

        inversion Hi1 as [Heqww']; subst; auto.
        inversion Hi1 as [Heqww']; subst; auto.

  (*Flush*)
    (*R*)
    intros [w r] Hr; rewrite Hr in Hs; apply flush_read_b_step with E p L s0 s1 phi; auto.

    (*W*)
    intros w Hw; rewrite Hw in Hs; unfold step in Hs; unfold flush_write_step in Hs.
    destruct (bin ((B s0)) w); [|inversion Hs];
    destruct (bemp
           (rrestrict (fun w1 w2 : Event => (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\ w1 = w)
              (fun e : Event => udr (Rcp s0) e))); [|inversion Hs].
    inversion Hs as [Heqs]; rewrite <- Heqs in Hi1; simpl in Hi1; contradiction.
Qed.

Lemma in_buff_implies_before :
  forall E p L lst n s0 s1 w phi,
  trans p ->
  events E w ->
  (B s1) w ->
  (exists d, trans d /\ rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
  p (d (DW w)) lst.
Proof.
intros E p L lst n s0 s2 w phi Htp Hew Hw Hm.
generalize lst s2 w Hew Hw Hm; 
clear lst s2 w Hew Hw Hm;
induction n; intros lst s2 w Hew Hw [d [Htd [Hid [Hni Hm]]]].

  destruct Hm as [Heqs [? [Hwfbi ?]]]; auto. 
  inversion Heqs as [Heq]; rewrite <- Heq in Hw.
  rewrite Hwfbi in Hw; inversion Hw. 

  destruct Hm as [l [s1 [Hl [Hm [Hs [Hwfb ?]]]]]].
  fold (machine E (pred d l) L l n phi (Some s0) (Some s1)) in Hm.
  assert (p l lst) as Hpllst.
    generalize (Last.last_in_ran d l Hl); intros [x' Hx].
    generalize (Hid x' l Hx); intros [? ?]; auto.
  generalize (excluded_middle ((B s1) w)); intros [Hib1|Hnib1].
    assert (exists d, trans d /\
            rel_incl d (pred p l) /\
            (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' l) \/
            Last.last d = l) /\ machine E d L l n phi (Some s0) (Some s1)) as Hex.
      exists (pred d l); split; [|split; [|split]]; auto.
        apply td_tpred; auto. 
        intros x' y [Hxy Hyl]; split; auto.
          generalize (Hid x' y Hxy); intros [? ?]; auto.
          generalize (Hid y l Hyl); intros [? ?]; auto.
          left; apply Last.no_interv_last; auto; intros x' y Hxy; generalize (Hid x' y Hxy); intros [? ?]; auto.
    generalize (IHn l s1 w Hew Hib1 Hex); intros Hpwl.

    apply Htp with l; auto.

  generalize (b_step E d L s1 s2 l w phi Hew Hnib1 Hw Hs); intro Heq;
  rewrite <- Heq; auto.
Qed.

Lemma nudr_udr :
  forall s w w',
  w <> w' ->
  w' <> dB ->
  ~ udr s w' ->
  udr (upd_buff s w) w' ->
  False.
Proof.
intros s w w' Hdiff Hndb Hnu Hu.
apply Hnu; unfold upd_buff in Hu.
destruct (bin (udr s) w); auto.
inversion Hu as [e [e' Hd] | e [e' Hr]].
  inversion Hd as [Hs | [[Heq | [Hran ?]] ?]].
    left; exists e'; auto.
    contradiction.
    right; auto.
  inversion Hr as [Hs | [Heq ?]].
    right; exists e'; auto.
    assert False as Ht.
      apply Hdiff; auto.
    inversion Ht.
Qed. 

Lemma rcp_step :
  forall E p L s0 s1 lb w phi,
  events E w ->
  ~(udr (Rcp s0) w) -> (udr (Rcp s1) w) ->
  step E p L (Some s0) lb phi = Some s1 ->
  lb = f (DW w).
Proof.
intros E p L s0 s1 lb w' phi Hew' Hni0 Hi1 Hs.
case_eq lb; intros de Hde; rewrite Hde in Hs; clear Hde; case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_read_step in Hs;
  destruct (okw E (B s0) w r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (bemp
             (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w)
                (fun e : Event =>
                 rel_seq (A.prop E (p2X E p L)) (AWmm.hb E (p2X E p L)) e r))); [|inversion Hs];
  inversion Hs as [Heq]; rewrite <- Heq in Hi1; contradiction.

  intros w Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_write_step in Hs;
  destruct (is_emp
           (Intersection Event (Rs s0) (fun r' : Event => A.fences E w r'))); [|inversion Hs];
  destruct (is_emp
            (Intersection _ (B s0)
               (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s0) (fun e : Event => A.prop E (p2X E p L) w e))); [|inversion Hs];
  inversion Hs as [Heq]; rewrite <- Heq in Hi1; contradiction.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde; unfold step in Hs; 
  unfold flush_resolved_read_step in Hs;
  destruct (bin (Rs s0) r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s0)
                (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (visible E (*p L*) s0 w r phi); [|inversion Hs].
  inversion Hs as [Heq]; rewrite <- Heq in Hi1; contradiction.

  intros w Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold flush_write_step in Hs.
  destruct (bin ((B s0)) w); [|inversion Hs].
  destruct (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
               w1 = w) (fun e : Event => udr (Rcp s0) e))); [|inversion Hs].
  inversion Hs as [Heq]; rewrite <- Heq in Hi1. 
  simpl in Hi1; unfold upd_rs in Hi1.
  destruct (eqEv_dec w w'); auto.
    subst; auto.
    assert (w' <> dB) as Hndb.
      apply dB_not_in_E with E; auto.
    generalize (nudr_udr (Rcp s0) w w' n Hndb Hni0 Hi1); intro Ht; inversion Ht.
Qed.

Lemma in_rcp_implies_f_before :
  forall E p (L:set Label) lst n s0 s1 w phi,
  trans p ->
  events E w ->
  udr (Rcp s1) w ->
  (*(forall w, L (f (DW w)) -> p (d (DW w)) (f (DW w))) ->*)
  (exists d, trans d /\ rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
  p (f (DW w)) lst.
Proof.
intros E p L lst n s0 s2 w phi Htp Hew Hw (*Hdf*) Hm.
generalize lst s2 w Hew Hw Hm; 
clear lst s2 w Hew Hw Hm;
induction n; intros lst s2 w Hew Hw [d [Htd [Hid [Hni Hm]]]].

  destruct Hm as [Heqs [? [? [? Hwfrcpi]]]]; auto. 
  inversion Heqs as [Heq]; rewrite <- Heq in Hw.
  rewrite Hwfrcpi in Hw; inversion Hw. 
    inversion Hw as [e [e' Ht] | e [e' Ht]]; inversion Ht.
    inversion Hw as [e [e' Ht] | e [e' Ht]]; inversion Ht.

  destruct Hm as [l [s1 [Hl [Hm [Hs [Hwfb ?]]]]]].
  fold (machine E (pred d l) L l n phi (Some s0) (Some s1)) in Hm.
  assert (p l lst) as Hpllst.
    generalize (Last.last_in_ran d l Hl); intros [x' Hx].
    generalize (Hid x' l Hx); intros [? ?]; auto.
  generalize (excluded_middle (udr (Rcp s1) w)); intros [Hib1|Hnib1].
    assert (exists d, trans d /\
            rel_incl d (pred p l) /\
            (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' l) \/
            Last.last d = l) /\ machine E d L l n phi (Some s0) (Some s1)) as Hex.
      exists (pred d l); split; [|split; [|split]]; auto.
        apply td_tpred; auto. 
        intros x' y [Hxy Hyl]; split; auto.
          generalize (Hid x' y Hxy); intros [? ?]; auto.
          generalize (Hid y l Hyl); intros [? ?]; auto.
          left; apply Last.no_interv_last; auto; intros x' y Hxy; generalize (Hid x' y Hxy); intros [? ?]; auto.
    generalize (IHn l s1 w Hew Hib1 Hex); intros Hpwl.

    apply Htp with l; auto.

  generalize (rcp_step E d L s1 s2 l w phi Hew Hnib1 Hw Hs); intro Heq.
  rewrite <- Heq; auto.
Qed.

Lemma rcp_p :
  forall E p L n s0 s1 lst w w' phi,
  well_formed_event_structure E ->
  linear_strict_order p L ->
  (exists d : Rln Label,
       trans d /\
       rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
  L (f (DW w')) ->
  wf_labels E L ->
  wf_buff E (Rcp s1) ->
  w <> dB ->
  Rcp s1 w w' -> loc w = loc w' ->
  p (f (DW w)) (f (DW w')).
Proof.
intros E p L n s0 s1 lst w w' phi Hwf Hlp Hm Hlfw' Hwfl Hwfb HndB Hww' Heql.
assert (events E w) as Hew.
  destruct Hwfb as [Hwb ?].
  assert (udr (Rcp s1) w) as Hudr.
    left; exists w'; auto.
  generalize (Hwb w Hudr); intros [? ?]; auto.
    assert (trans p) as Htp.
      destruct_lin Hlp; auto.
      intros x1 x2 x3 H12 H23; apply Htrans with x2; auto.
generalize lst s1 Hwfb Hww' Hm; 
clear lst s1 Hwfb Hww' Hm; 
induction n; intros lst s1 Hwfb Hww' Hm.

  destruct Hm as [? [? [? [? Hm]]]]; auto.
  destruct Hm as [Heqs [? [? [? Hwfbi]]]]; auto. 
  inversion Heqs as [Heq]; rewrite <- Heq in Hww'.
  assert (udr (Rcp s0) w) as Hudr.
    left; exists w'; auto.
  rewrite Hwfbi in Hudr; inversion Hudr as [? Hi | ? Hi]; 
    inversion Hi as [? Ht]; inversion Ht.

destruct Hm as [r [Htr [Hir [Hnir [l [s [Hl [Hm [Hs [? [? [Hwfbs ?]]]]]]]]]]]];
fold (machine E (pred r l) L l n phi (Some s0) (Some s)) in Hm.
assert (exists r,
        trans r /\
        rel_incl r (pred p l) /\
        (~ (exists l', tc p (Last.last r) l' /\ tc p l' l) \/ 
        Last.last r = l) /\ machine E r L l n phi (Some s0) (Some s)) as Hed.
  exists (pred r l); split; [|split; [|split]]; auto.
  apply td_tpred; auto. 
  intros x y [Hxy Hyl]; 
  generalize (Hir x y Hxy); intros [? ?];
  generalize (Hir y l Hyl); intros [? ?]; split; auto.
  left; apply Last.no_interv_last; auto; intros x y Hxy; 
    generalize (Hir x y Hxy); intros [? ?]; auto.

destruct (eqLabel_dec (f (DW w')) l) as [Heqw'l | Hneqw'l].

rewrite <- Heqw'l in Hs; simpl in Hs; unfold flush_write_step in Hs.
  destruct (bin (B s) w'); [|inversion Hs].
  destruct (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ A.prop E (p2X E r L) w1 w2) /\ w1 = w')
              (fun e : Event => udr (Rcp s) e))); [|inversion Hs].
inversion Hs as [Heqs].
rewrite <- Heqs in Hww'; simpl in Hww'.
unfold upd_buff in Hww'.
    assert (udr (Rcp s) w) as Hudr.
      destruct (bin (udr (Rcp s)) w').
        left; exists w'; auto.
        inversion Hww' as [? | [Hor ?]].
          left; exists w'; auto.
          inversion Hor as [HdB | [Hr ?]].
            rewrite HdB in Hew; generalize (dB_not_in_E E dB Hew); 
            intro Hn; assert False as Ht.
            apply Hn; auto. inversion Ht.
          right; auto.
          
    generalize (in_rcp_implies_f_before E p L l n s0 s w phi Htp Hew Hudr Hed); intros;
    rewrite Heqw'l; auto.

assert (L (f (DW w'))) as Hlw'.
  auto.
assert (L l) as Hll.
  generalize (Last.last_in_ran r l Hl); intros [x Hx].
  generalize (Hir x l Hx); intros [? ?].
    destruct_lin Hlp; apply Hdr; left; exists lst; auto.

generalize (excluded_middle ((Rcp s) w w')); intros [Hb | Hnb].

  generalize (IHn l s Hwfbs Hb Hed). auto.

  destruct (eqEv_dec w w') as [Heq | Hneq].
    rewrite Heq in Hww'; destruct Hwfb as [? [? [Hac ?]]].
    assert (tc (rrestrict (Rcp s1) (fun w => loc w = loc w')) w' w') as Hc.
      apply trc_step; split; auto; split; unfold Ensembles.In; auto.
    generalize (Hac w' w' Hc); intro Ht; inversion Ht.

  assert (udr (Rcp s1) w') as Hudrs1.
    right; exists w; auto.

  assert (events E w') as Hew'.
    destruct Hwfb as [Hibw ?].
      assert (w' <> dB) as HndB'.
        intro Heq; rewrite Heq in Hww'; apply (dB_not_ran (Rcp s1)); exists w; auto.
      generalize (Hibw w' Hudrs1 HndB'); intros [? ?]; auto.

  generalize (excluded_middle (udr (Rcp s) w)); intros [Hbw | Hnbw].
  Focus 2.
    assert (udr (Rcp s1) w) as Hudr.
      left; exists w'; auto.
    generalize (rcp_step E r L s s1 l w phi Hew Hnbw Hudr Hs); intro Heq.
    assert False as Ht.    
      apply rcp_swap_contrad' with E r L s s1 w w' phi; auto.
      rewrite Heq in Hs; auto.
    inversion Ht.    

    assert (ran (Rcp s) w) as Hran.
      exists dB; generalize (udr_dB (Rcp s) w); intros [dir ?]; apply (dir Hbw).
    generalize (excluded_middle (udr (Rcp s) w')); intros [Hudr' | Hnudr'].

    assert (ran (Rcp s) w') as Hrw'.
      exists dB; generalize (udr_dB (Rcp s) w'); intros [dir ?]; apply (dir Hudr').
    generalize Hwfbs; intros Hwfbs'; destruct Hwfbs as [? [Htb ?]]; 
    generalize (Htb w w' Hew Hew' Hneq Hran Hrw' Heql); intros [Hbsww' | Hbsw'w].
    assert False as Ht.
      apply Hnb; auto.
    inversion Ht.
    assert False as Ht.    
      apply rcp_swap_contrad with E r L l s s1 w' w phi; auto.
    inversion Ht.

    generalize (rcp_step E r L s s1 l w' phi Hew' Hnudr' Hudrs1 Hs); intro Heq.
    rewrite <- Heq; apply in_rcp_implies_f_before with E L n s0 s phi; auto.
Qed.

(*Lemma rcp_p :
  forall E p L n s0 s1 lst w w' phi,
  well_formed_event_structure E ->
  linear_strict_order p L ->
  (exists d : Rln Label,
       trans d /\
       rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
  wf_labels E L ->
(*  wf_rf_labels E L ->
  wf_l_p E p L ->*)
  wf_buff E (Rcp s1) ->
  w <> dB ->
  Rcp s1 w w' -> loc w = loc w' ->
  p (f (DW w)) (f (DW w')).
Proof.
intros E p L n s0 s1 lst w w' Hwf Hlp Hm Hwfl (*Hwfrfl Hwflp*) Hwfb HndB Hww' Heql.

  assert (f (DW w) <> f (DW w')) as Hd.
    intro Heq; inversion Heq as [Heqe]; rewrite Heqe in Hww'.
    assert (tc (rrestrict (Rcp s1) (fun e => loc e = loc w')) w' w') as Hc.
      apply trc_step; split; auto; split; unfold Ensembles.In; auto.
    destruct Hwfb as [? [Ht [Hac ?]]]; apply (Hac w' w' Hc).
assert (L (f (DW w))) as Hlfw.
  apply wfl_w with E; auto.
    destruct Hwfb as [Hw ?]; apply Hw; auto. 
      left; exists w'; auto.
assert (L (f (DW w'))) as Hlfw'.
  apply wfl_w with E; auto.
    destruct Hwfb as [Hw ?]; apply Hw; auto.
    right; exists w; auto.    
    intro Heq; assert (ran (Rcp s1) dB) as Hr.
      exists w; rewrite <- Heq; auto. 
    apply (dB_not_ran (Rcp s1) Hr).
destruct_lin Hlp; generalize (Htot (f (DW w)) (f (DW w')) Hd Hlfw Hlfw');
intro Hor; inversion Hor as [|Hp]; clear Hor; auto.

(*generalize (Hmns (f (DW w)) Hlfw);
intros [m [s [s' [s'' [Hwfb' [Hwfrs' [Hwfcs' [Hwfrcp' [Hm Hs]]]]]]]]];
simpl in Hs; unfold flush_write_step in Hs.
destruct (bin (B s') w); [|inversion Hs].
case_eq (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = w)
              (fun e : Event => udr (Rcp s') e))); intro Hb;
rewrite Hb in Hs; [|inversion Hs].
generalize (bemp_axt (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = w) (fun e : Event => udr (Rcp s') e) Hb);
clear Hb; intro Hn.

assert (trans p) as Htp.
  intros x y z Hxy Hyz; apply Htrans with y; auto.
assert (acyclic p) as Hacp.
  intros x Hx; apply Hac with x; rewrite <- trans_tc with Label p; auto.*)

  assert False as Ht.
    apply Hn; exists w'; split; auto.
    exists w; split; auto; left; auto.
      apply b_persistent with E p L (f (DW w)) m s1 s; auto.
      apply Htp with (f (DW w')); auto.
        apply p_dw_fw with E L; auto.
          split; [|split]; auto.

        exists (pred p (f (DW w))); split; [|split; [|split]]; auto.
          apply td_tpred; auto.
          intros x y Hxy; auto.
          left; apply Last.no_interv_last; auto; intros x y Hxy; auto.            
          destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.

      apply in_order_implies_in_rcp with E p L (f (DW w)) m s (f (DW w)); auto.
        exists (pred p (f (DW w))); split; [|split; [|split]]; auto.
          apply td_tpred; auto. intros x y Hxy; auto.
          apply Last.no_interv_last; auto; intros x y Hxy; auto.
  inversion Ht.
Qed. *)

Lemma p_rcp :
  forall E p L lst n s0 s1 w w' phi,
  well_formed_event_structure E ->
  linear_strict_order p L ->
  wf_labels E L ->
  (exists d : Rln Label,
       trans d /\
       rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
  wf_buff E (Rcp s1) ->
  loc w = loc w' ->
  Rcp s1 dB w -> Rcp s1 dB w' ->
  p (f (DW w)) (f (DW w')) ->
  L (f (DW w)) ->
  Rcp s1 w w'.
Proof.
intros E p L lst n s0 s1 w w' phi Hwf Hlp Hwfl Hm Hwfb Hloc Hw Hw' Hp Hlfw.
assert (Rcp s1 w w' \/ Rcp s1 w' w) as Hor.
  destruct Hwfb as [Hbw [Htb ?]].
  apply Htb; auto.
    assert (ran (Rcp s1) w) as Hran.
      exists dB; auto.
    assert (udr (Rcp s1) w) as Hudr.
      right; auto.
    assert (w <> dB) as HndB.
      intro Heq; rewrite Heq in Hran; apply (dB_not_ran (Rcp s1) Hran).   
    generalize (Hbw w Hudr HndB); intros [? ?]; auto.
    assert (ran (Rcp s1) w') as Hran.
      exists dB; auto.
    assert (udr (Rcp s1) w') as Hudr.
      right; auto.
    assert (w' <> dB) as HndB.
      intro Heq; rewrite Heq in Hran; apply (dB_not_ran (Rcp s1) Hran).   
    generalize (Hbw w' Hudr HndB); intros [? ?]; auto.
    intro Heq; rewrite Heq in Hp.
    destruct_lin Hlp; apply Hac with (f (DW w')); auto.
    exists dB; auto. exists dB; auto.
inversion Hor as [|Hw'w]; clear Hor; auto.
assert (loc w' = loc w) as Hloc'.
  apply sym_eq; auto.
assert (w' <> dB) as HndB.
  intros Heq; rewrite Heq in Hw'.
  assert (ran (Rcp s1) dB) as Hr.
    exists dB; auto.
  apply (dB_not_ran (Rcp s1) Hr); auto. 

generalize (rcp_p E p L n s0 s1 lst w' w phi Hwf Hlp Hm Hlfw Hwfl Hwfb HndB Hw'w Hloc'). 
intros.
destruct_lin Hlp; assert (p (f (DW w)) (f (DW w))) as Hc.
  apply Htrans with (f (DW w')); auto.
generalize (Hac (f (DW w)) Hc); intro Ht; inversion Ht.
Qed.

Lemma if_ldw_then_lfw :
  forall E L w, wf_labels E L ->
  L (d (DW w)) -> L (f (DW w)).
Proof.
intros E L w [[Hdw ?] [? [Hwlf ?]]] Hld; apply Hwlf; apply Hdw; auto.
Qed.
Lemma if_ldr_then_lfr :
  forall E L w r, wf_labels E L -> wf_rf_labels E L ->
  L (d (DR (w,r))) -> L (f (DR (w,r))).
Proof.
intros E L w r [? [[Hld Hlf] [? Hdf]]] Hwfrfl Hdr.
generalize (Hld w r Hdr); intros [? [? Hrfm]].
assert (reads E r) as Hrr.
  split; auto.
    destruct Hrfm as [l [? [[v Har] ?]]]; exists l; exists v; auto.
destruct Hwfrfl as [Hrl [Hdeq ?]]; generalize (Hrl r Hrr);
intros [wr [Hrfm' Hfl']].
generalize (Hdf (DR (wr,r)) Hfl'); intro Hdl.
generalize (Hdeq r w wr Hdr Hdl); intro Heq; rewrite Heq; auto.
Qed. 

(*Lemma in_order_implies_in_obuff : 
  forall E p L lst n s0 s1 w1 w2 lb,
  well_formed_event_structure E ->
  wf_buff E (B s1) ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->  
  loc w1 = loc w2 ->
  (forall l, L l -> events E (evt_of_label l) ) ->
  p (d (DW w1)) (d (DW w2)) ->
  p (d (DW w2)) lb -> p (d (DW w2)) lst ->
  wf_labels E L ->
  (~ (exists l' : Label, tc p lst l' /\ tc p l' lb) \/ lst = lb) ->
  (exists d, trans d /\ rel_incl d (pred p lst) /\ 
     (~(exists l', tc p (Last.last d) l' /\ tc p l' lst) \/ Last.last d = lst) /\
     machine E d L lst n (Some s0) (Some s1)) ->
  B s1 w1 w2.
Proof.
intros E p L lst n s0 s2 w1 w2 lb'' Hwf Hwfb Hudrp Htp Hacp Htotp Heqloc Hle 
  Hp12 Hpw2lb'' Hpw2lst Hwfl Hni Hm.

  assert (p (d (DW w1)) lst) as Hpw1lb''.
    apply Htp with (d (DW w2)); auto.
  assert (p (d (DW w1)) lst) as Hpw1lst.
    apply Htp with (d (DW w2)); auto.

  assert (L (f (DW w1))) as Hlfw1.
    apply if_ldw_then_lfw with E; auto.
    apply Hudrp; left; exists lst; auto.
  assert (L (f (DW w2))) as Hlfw2.
    apply if_ldw_then_lfw with E; auto.
    apply Hudrp; right; exists (d (DW w1)); auto.
  assert (~ (exists l', tc p lst l' /\ tc p l' lst) \/ lst = lst) as Hni'.
    auto.
  generalize (in_order_implies_in_buff E p L lst n s0 s2 w1 lst Hwfl Hudrp Htp Hacp Htotp 
                Hle Hpw1lb'' Hpw1lst Hlfw1 Hni' Hm); intros Hi1; auto.
  generalize (in_order_implies_in_buff E p L lst n s0 s2 w2 lb'' Hwfl Hudrp Htp Hacp Htotp 
                Hle Hpw2lb'' Hpw2lst Hlfw2 Hni Hm); intros Hi2; auto.
  
  generalize Hwfb; intros Hwfb2; destruct Hwfb as [Hibw [Htot ?]].
  assert (w1 <> w2) as Hdiff.
    intro Heq; rewrite Heq in Hp12.
    apply Hacp with (d (DW w2)); apply trc_step; auto.
  assert (ran (B s2) w1) as Hr1.
    exists dB; auto.
  assert (ran (B s2) w2) as Hr2.
    exists dB; auto.  
  assert (w1 <> dB) as HndB1.
    intro Heq; rewrite Heq in Hr1; apply (dB_not_ran (B s2) Hr1).
  assert (w2 <> dB) as HndB2.
    intro Heq; rewrite Heq in Hr2; apply (dB_not_ran (B s2) Hr2).
  assert (udr (B s2) w1) as Hu1.
    right; auto.
  assert (udr (B s2) w2) as Hu2.
    right; auto.
  generalize (Hibw w1 Hu1 HndB1); intros [He1 ?].
  generalize (Hibw w2 Hu2 HndB2); intros [He2 ?].
  generalize (Htot w1 w2 He1 He2 Hdiff Hr1 Hr2 Heqloc); intros [|H21]; auto.  
  assert (linear_strict_order p L) as Hlp.
    split; [|split; [|split]]; auto.
    intros x1 x2 x3 [H12 H23]; apply Htp with x2; auto.
    intros x Hx; apply Hacp with x; apply trc_step; auto.
  apply (p_b E p L lst n s0 s2 w1 w2 Hwf Hlp Hwfl Hm Hwfb2 Heqloc Hi1 Hi2 Hp12); auto.
Qed.*)

(*Lemma in_buff_implies_in_order' :
  forall E (p:Rln Label) (L:set Label) lst n s0 s1 w1 w2,
  well_formed_event_structure E ->
  wf_labels E L ->
  (forall l : Label, L l -> events E (evt_of_label l)) ->
  L (d (DW w1)) -> L (d (DW w2)) ->
  loc w1 = loc w2 -> 
  (exists d, trans d /\ rel_incl d (pred p lst) /\
     (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/ Last.last d = lst) /\
     machine E d L lst n (Some s0) (Some s1)) ->
  Included Label (Union Label (dom p) (ran p)) L ->
  trans p ->
  acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->  
  wf_buff E (B s1) ->
  (B s1) w1 w2 ->
  tc p (d (DW w1)) (d (DW w2)).
Proof.
intros E p L lst n s0 s2 w1 w2 Hwf Hwfl Hle Hl1 Hl2 Heqloc Hm Hudrp Htp Hacp Htotp Hwfb Hb.

assert (p (d (DW w1)) lst) as Hor1lst. 
  apply (in_buff_implies_before E p L lst n s0 s2 w1); auto.
    assert (w1 = evt_of_label (d (DW w1))) as Heq.
      simpl; auto.
    rewrite Heq; apply Hle; auto.
    left; exists w2; auto.

assert (d (DW w1) <> d (DW w2)) as Hdiff.
  intro Heql; inversion Heql as [Heq]; rewrite Heq in Hb.
  destruct Hwfb as [? [? [Hac ?]]].
  generalize (Hac w2); clear Hac; intro Hac.
  assert (tc (rrestrict (B s2) (fun w => loc w = loc w2)) w2 w2) as Hc.
    apply trc_step; split; [|split]; auto; unfold Ensembles.In; auto.
  apply Hac with w2; auto.

generalize (Htotp (d (DW w1)) (d (DW w2)) Hdiff Hl1 Hl2); intros [|H21]; apply trc_step; auto.
assert (loc w2 = loc w1) as Heqloc'.
  apply sym_eq; auto.
assert (~ (exists l' : Label, tc p lst l' /\ tc p l' lst) \/ lst = lst) as Hni'.
  auto.

generalize (in_order_implies_in_obuff E p L lst n s0 s2 w2 w1 lst Hwf Hwfb Hudrp Htp Hacp Htotp 
  Heqloc' Hle H21 Hor1lst Hor1lst Hwfl Hni' Hm); intros Hb21; auto.
(*HERE*)

  destruct Hwfb as [? [? [Hac ?]]].
  assert (tc (rrestrict (B s2) (fun w => loc w = loc w1)) w1 w1) as Hc.
    apply trc_ind with w2; apply trc_step; split; auto; split; unfold Ensembles.In; auto.
  generalize (Hac w1 w1 Hc); intro Ht; inversion Ht.
Qed. *)

Lemma udr_upd_rcp :
  forall s w w',
  udr s w' ->
  udr (upd_buff s w) w'.
Proof.
intros s w w' [e [e' Hd] | e [e' Hr]].
  left; exists e'; unfold upd_buff; destruct (bin (udr s) w); auto; left; auto.
  right; exists e'; unfold upd_buff; destruct (bin (udr s) w); auto; left; auto.
Qed.

Lemma same_rcp :
  forall E (p:Rln Label) L s0 s1 lb w phi,
  events E w ->
  step E p L (Some s0) lb phi = Some s1 ->
  wf_rf_labels E L ->
  udr (Rcp s0) w ->
  udr (Rcp s1) w.
Proof.
intros E p L s0 s1 lb w' phi Hew' Hs Hwfrf Hi0.
case_eq lb; intros de Hde; rewrite Hde in Hs; clear Hde; case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_read_step in Hs;
  destruct (okw E (B s0) w r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (bemp
             (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w)
                (fun e : Event =>
                 rel_seq (A.prop E (p2X E p L)) (AWmm.hb E (p2X E p L)) e r))); [|inversion Hs];
  inversion Hs as [Heq]; auto. 

  intros w Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_write_step in Hs;
  destruct (is_emp
           (Intersection Event (Rs s0) (fun r' : Event => A.fences E w r'))); [|inversion Hs];
  destruct (is_emp
            (Intersection _ (B s0)
               (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s0) (fun e : Event => A.prop E (p2X E p L) w e))); [|inversion Hs];
  inversion Hs as [Heq]; auto.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde; unfold step in Hs; 
  unfold flush_resolved_read_step in Hs;
  destruct (bin (Rs s0) r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s0)
                (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (visible E (*p L*) s0 w r phi); [|inversion Hs].
  inversion Hs as [Heq]; auto.

  intros w Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold flush_write_step in Hs.
  destruct (bin ((B s0)) w); [|inversion Hs].
  destruct (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
               w1 = w) (fun e : Event => udr (Rcp s0) e))); [|inversion Hs].
  inversion Hs as [Heq]; auto.
  simpl; auto.
  apply udr_upd_rcp; auto.
Qed.

Lemma in_order_implies_in_rcp :
  forall E (p:Rln Label) L lst n s0 s1 lb w phi,
  Included _ (Union _ (dom p) (ran p)) L ->  
  trans p ->
  acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->  
  wf_rf_labels E L ->
  L lb -> 
  p (f (DW w)) lb -> p (f (DW w)) lst ->
  w <> dB ->
  wf_buff E (Rcp s1) ->
  (~ (exists l' : Label, tc p lst l' /\ tc p l' lb) \/ lst = lb) ->
  (exists d, trans d /\ rel_incl d (pred p lb) /\ 
     ~(exists l', tc p (Last.last d) l' /\ tc p l' lst) /\
     machine E d L lst n phi (Some s0) (Some s1)) ->
  udr (Rcp s1) w.
Proof.
intros E p L lst n s0 s2 lb'' w phi Hudrp Htp Hacp Htotp Hwfr Hllb Hprlb Hprlst Hndb Hwfrcp Hni Hm.
generalize s2 lst lb'' Hwfr Hm Hllb Hprlb Hprlst Hwfrcp Hni; 
clear s2 lst lb'' Hwfr Hm Hllb Hprlb Hprlst Hwfrcp Hni; 
induction n; 
intros s2 lst lb'' Hwfr [pd [Htd [Hi [Hniw Hm]]]] Hllb Hprlb Hprlst Hwfrcp Hni.
  
  destruct Hm as [? [Heof ?]]; auto.
    assert False as Ht.
      apply Hniw; rewrite Heof; exists (f (DW w)); split; auto;
      apply trc_step; auto. apply EOF_bef; auto.
    inversion Ht.

  destruct Hm as [lb [s1 [Hdlb [Hm [Hs [? [Hwfq [Hwfrcp' Hwfcs]]]]]]]];
  fold (machine E (pred pd lb) L lb n phi (Some s0) (Some s1)) in Hm.
  destruct (eqLabel_dec lb (f (DW w))) as [Heqlbr | Hneqlbr].
    rewrite Heqlbr in Hs; unfold step in Hs; unfold flush_write_step in Hs.
    destruct (bin ((B s1)) w); [|inversion Hs];
    destruct (bemp
            (rrestrict
               (fun w1 w2 : Event =>
                (po_loc E w1 w2 \/ (A.prop E (p2X E pd L)) w1 w2) /\
                w1 = w) (fun e : Event => udr (Rcp s1) e))); [|inversion Hs].
  inversion Hs as [Heqs]; simpl; auto.
  right; unfold Ensembles.In; auto. 
    exists dB; unfold upd_buff; case_eq (bin (udr (Rcp s1)) w); intro Hudr; auto.
      generalize (udr_dB (Rcp s1) w); intros [Hd Hc]; auto.
      generalize (bin_In (udr (Rcp s1)) w Hudr); clear Hudr; intro Hudr.
      generalize (Hd Hudr); intros [? ?]; auto.
      right; split; auto.

  assert (exists d, trans d /\ rel_incl d (pred p lb) /\
          ~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lb) /\
          machine E d L lb n phi (Some s0) (Some s1)) as Hex.
    exists (pred pd lb); split; [|split; [|split]]; auto. 
      apply (td_tpred pd lb Htd).
      intros x y [Hxy Hylb]; 
      generalize (Hi x y Hxy); intros [? ?];
      generalize (Hi y lb Hylb); intros [? ?]; split; auto.
      apply Last.no_interv_last; auto. 
        intros x y Hxy; generalize (Hi x y Hxy); intros [? ?]; auto.
  assert (L lb) as Hlb.
    apply Hudrp; auto.
    generalize (Last.last_in_ran pd lb Hdlb); intros [x Hx];
    generalize (Hi x lb Hx); intros [? ?]; right; exists x; auto.
  assert (~ (exists l' : Label, tc p lb l' /\ tc p l' lb) \/ lb = lb) as Hnieq.
    auto.
  assert (p (f (DW w)) lb) as Hrlb.
    assert (L (f (DW w))) as Hlr.
      apply Hudrp; left; exists lb''; auto.
    generalize (Htotp lb (f (DW w)) Hneqlbr Hlb Hlr); intros [Hlbr | ?]; auto.
    assert (exists l' : Label, tc p (Last.last pd) l' /\ tc p l' lst) as Hc.
      rewrite Hdlb; exists (f (DW w)); split; apply trc_step; auto.
    contradiction.
  generalize (IHn s1 lb lb Hwfr Hex Hlb Hrlb Hrlb Hwfrcp' Hnieq); intro Hi1.

  apply (same_rcp E pd L s1 s2 lb w phi); auto.
    destruct Hwfrcp' as [Hwfrcp' ?]; generalize (Hwfrcp' w Hi1); intros [? ?]; auto.
Qed.

Lemma p_dw_fw :
  forall E p L w phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  L (f (DW w)) ->
  p (d (DW w)) (f (DW w)).
Proof.
intros E p L w phi Hwf Hwfl Hwfrfl Hlp Hmns Hlf.
assert (d (DW w) <> f (DW w)) as Hdiff.
  intro Heq; inversion Heq.
destruct_lin Hlp.
assert (p (d (DW w)) (f (DW w)) \/ p (f (DW w)) (d (DW w))) as Hor.
  apply Htot; auto.
  destruct Hwfl as [? [? [? Hfd]]]; apply Hfd; auto.
inversion Hor as [|Hfd]; clear Hor; auto.
generalize (Hmns (f (DW w)) Hlf); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_write_step in Hs.
case_eq (bin ((B s1)) w); intro Hi; rewrite Hi in Hs; [|inversion Hs].
assert (trans p) as Htp.
  intros x y z Hxy Hyz; apply Htrans with y; auto.
rewrite <- trans_tc with Label p; auto.
apply in_buff_implies_before with E L n s0 s1 phi; auto.
  intros x y z Hxy Hyz; apply trc_ind with y; auto.
  destruct Hwfl as [[? Hfw] ?].
  generalize (Hfw w Hlf); intros [? ?]; auto.
  apply bin_In; auto.
  exists (pred p (f (DW w))); split; [|split; [|split]]; auto.
    apply td_tpred; auto.
    intros x y Hxy; auto.
    rewrite trans_tc; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.
      apply trc_step; auto.
Qed. 

Lemma ws_rcp :
  forall E p L lst n s0 s1 w w' phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  (*wf_l_p E p L ->*)
  wf_buff E (Rcp s1) ->
  linear_strict_order p L ->
  (exists d : Rln Label,
       trans d /\
       rel_incl d (pred p lst) /\
       (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lst) \/
        Last.last d = lst) /\ machine E d L lst n phi (Some s0) (Some s1)) ->
(*  machine_not_stuck E p L ->*)
  ran (Rcp s1) w -> ran (Rcp s1) w' ->
  ws (p2X E p L) w w' -> 
  Rcp s1 w w'.
Proof.
intros E p L lst n s0 s1 w w' phi Hwf Hwfl Hwfrfl (*Hwflp*) Hwfb Hlp Hmns Hbw Hbw' Hws;
  generalize Hwfb; intros [? [Ht Hacb]]. 
assert (forall w, writes E w -> L (f (DW w))) as Hlw.
  apply wfl_w; auto.
assert (loc w = loc w') as Hl.
  apply ABasic.ws_implies_same_loc with E (p2X E p L); auto.
    split; [apply path_ws_wf | apply path_rf_wf]; auto.
assert (w <> w') as Hd.
  generalize (path_ws_wf E p L Hlw Hlp); intros [Hlin ?].
  generalize (Hlin (loc w)); intros [? [? [Hac ?]]].
  generalize (path_ws_wf E p L Hlw Hlp); intro Hwswf.
  intro Heq; apply Hac with w; split; auto.
    rewrite <- Heq in Hws; auto.
      split; split. 
        apply ABasic.dom_ws_in_events with (p2X E p L) w'; auto.
        generalize (ABasic.dom_ws_is_write E (p2X E p L) w w' Hwswf Hws); intros [? [v Haw]];
          exists v; unfold loc; rewrite Haw; auto.
        apply ABasic.dom_ws_in_events with (p2X E p L) w'; auto.
        generalize (ABasic.dom_ws_is_write E (p2X E p L) w w' Hwswf Hws); intros [? [v Haw]];
          exists v; unfold loc; rewrite Haw; auto.
assert (events E w) as Hew.
  apply ABasic.dom_ws_in_events with (p2X E p L) w'; auto.
  apply path_ws_wf; auto.
assert (events E w') as Hew'.
  apply ABasic.ran_ws_in_events with (p2X E p L) w; auto.
  apply path_ws_wf; auto.

generalize (Ht w w' Hew Hew' Hd Hbw Hbw' Hl); intro Hor; inversion Hor as [? | Hw'w]; auto.
assert (p (f (DW w)) (f (DW w'))) as Hp.
  destruct Hws as [Hw1 [Hw2 [? [l1 [l2 [H1 [H2 Hp]]]]]]]; subst; auto.

  assert (loc w' = loc w) as Hl'.
    apply sym_eq; auto.
  assert (w' <> dB) as HndB.
    intro Heq.
    assert (ran (Rcp s1) dB) as Hr.
      rewrite Heq in Hbw'; auto.
    apply (dB_not_ran (Rcp s1) Hr); auto.
  assert (L (f (DW w))) as Hlfw.
    destruct_lin Hlp.
    apply Hdr; left; exists (f (DW w')); auto.

  generalize (rcp_p E p L n s0 s1 lst w' w phi Hwf Hlp Hmns Hlfw Hwfl Hwfb HndB Hw'w Hl'); intro Hc. 
  assert (p (f (DW w)) (f (DW w')) /\ p (f (DW w')) (f (DW w))) as Hand.
    split; auto. 
  destruct_lin Hlp; generalize (Hac (f (DW w)) (Htrans (f (DW w)) (f (DW w')) (f (DW w)) Hand));
  intro Hf; inversion Hf.
Qed.

Lemma path_uniws : 
  forall E p (L:set Label) e1 e2 phi,
  well_formed_event_structure E ->
  wf_labels E L ->
  wf_rf_labels E L ->
  (*Included _ (Union _ (dom p) (ran p)) L ->
  acyclic p ->*)
 linear_strict_order p L ->
  (forall e1 e2, L (d (DW e1)) -> L (d (DW e2)) -> po_iico E e1 e2 -> loc e1 = loc e2 -> p (d (DW e1)) (d (DW e2))) ->
(*  (forall w w', loc w = loc w' -> tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  machine_not_stuck E p L phi ->
  po_loc_llh E e1 e2 -> ~ ws (p2X E p L) e2 e1.
Proof.
intros E p L e1 e2 phi Hwf Hwfl Hwfrfl Hlp Hpod (*Hfifo*) Hmns H12 Hws.
simpl in Hws; unfold p2ws in Hws; destruct Hws as [Hw1 [Hw2 [Heql [l2 [l1 [Hf2 [Hf1 Hp]]]]]]].

    assert (p (d (DW e1)) (d (DW e2))) as Hp12.
       destruct_lin Hlp; apply Hpod; destruct H12 as [? [? ?]]; auto.
       destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; apply Hdr; right; exists l2; rewrite Hf1 in Hp; auto.
       destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; apply Hdr; left; exists l1; rewrite Hf2 in Hp; auto.

    rewrite Hf2 in Hp; rewrite Hf1 in Hp.
    generalize Hlp; intro Hlp'; destruct_lin Hlp';
    apply (Hac (d (DW e1))). 
    apply Htrans with (d (DW e2)); split; auto.

    assert (L (f (DW e1))) as Hl1.
      apply Hdr; right; exists (f (DW e2)); auto.
    assert (L (f (DW e2))) as Hl2.
      apply Hdr; left; exists (f (DW e1)); auto.

    assert (trans p) as Htp.
      intros x y z Hxy Hyz; apply Htrans with y; auto.
    assert (acyclic p) as Hacp.
      intros x Hx; apply Hac with x; rewrite trans_tc in Hx; auto.

    generalize (Hmns (f (DW e1)) Hl1);
    intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfcs [Hwfrcp [Hm Hs]]]]]]]]].
    assert (exists d, trans d /\ rel_incl d (pred p (f (DW e1))) /\
    (~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' (f (DW e1))) \/
     Last.last d = (f (DW e1))) /\ machine E d L (f (DW e1)) n phi (Some s0) (Some s1)) as Hexd.
      exists (pred p (f (DW e1))); split; [|split; [|split]]; auto.
      apply td_tpred; auto.   
      intros x y Hxy; auto.
      left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

    assert (p (d (DW e1)) (f (DW e1))) as Hpdf1.
      apply p_dw_fw with E L phi; auto.
    assert (p (d (DW e2)) (f (DW e1))) as Hpd2f1.
      apply Htp with (f (DW e2)); auto. 
      apply p_dw_fw with E L phi; auto.

    assert (B s1 e1) as Hb1.
      apply in_order_implies_in_buff with E p L (f (DW e1)) n s0 (f (DW e1)) phi; auto.
        apply wfl_e; auto.

    assert (B s1 e2) as Hb2.
      apply in_order_implies_in_buff with E p L (f (DW e1)) n s0 (f (DW e1)) phi; auto.
        apply wfl_e; auto.

(*    apply sym_eq in Heql;
    generalize (p_b E p L (f (DW e1)) n s0 s1 e1 e2 Hwf Hlp Hwfl Hexd Hwfb Heql Hb1 Hb2 Hp12 Hl1); intro Hb12.*)
    unfold step in Hs; unfold flush_write_step in Hs.
    destruct (bin (B s1) e1); [|inversion Hs].
    case_eq (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = e1)
              (fun e : Event => udr (Rcp s1) e))); intro Hb; rewrite Hb in Hs; [|inversion Hs].
    generalize (bemp_axt (fun w1 w2 => (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = e1) 
                  (fun e : Event => udr (Rcp s1) e) Hb); intro Hn.
    assert (exists e : Event,
            ran (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = e1) e /\
            udr (Rcp s1) e) as Hy.
      exists e2; split; auto.
        exists e1; split; auto; left; auto.
          destruct H12 as [? [? ?]]; split; auto.
          apply in_order_implies_in_rcp with E p L (f (DW e1)) n s0 (f (DW e1)) phi; auto.
            apply dB_not_in_E with E; auto.
              destruct Hw1 as [? ?]; auto.
            exists (pred p (f (DW e1))); split; [|split; [|split]]; auto.
              apply td_tpred; auto. 
              intros x y Hxy; auto.
              apply Last.no_interv_last; auto; intros x y Hxy; auto.
    contradiction.
Qed.

Lemma path_uniwsrf : 
  forall E p L e1 e2 phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p -> 
  (forall w, writes E w -> L (f (DW w))) ->
  (forall w1 r1 w2, L (f (DR (w1, r1))) -> L (d (DW w2)) -> 
     po_iico E r1 w2 -> loc r1 = loc w2 -> p (f (DR (w1,r1))) (d (DW w2))) ->
  (forall e3 e4 : Event, L (d (DW e3)) -> L (d (DW e4)) -> po_iico E e3 e4 -> loc e3 = loc e4 -> p (d (DW e3)) (d (DW e4))) ->
  (*(forall w w' : Event,
    loc w = loc w' -> tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  machine_not_stuck E p L phi -> wf_labels E L -> wf_rf_labels E L ->
  po_loc_llh E e1 e2 -> ~ (rel_seq (ws (p2X E p L)) (rf (p2X E p L))) e2 e1.
Proof.
intros E p L e1 e2 phi Hwf Hudrp Htp Hacp Hlw Hpop Hpoww (*Hfifo*) Htotp Hmns Hwfl Hwfrfl 
H12 [e [Hws Hrf']].
generalize H12; intros [Heql12 [Hpo12 ?]].
generalize Hrf'; intro Hrf.
generalize Hws; intro Hws'.
simpl in Hws; unfold p2ws in Hws; destruct Hws as [Hw1 [Hw2 [Heqlw [l1 [l2 [Hf1 [Hf2 Hp]]]]]]].
simpl in Hrf; unfold p2rf in Hrf; destruct Hrf as [? Hfl].

assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros x y z [Hxy Hyz]; apply Htp with y; auto.
    intros x Hx; apply Hacp with x; apply trc_step; auto.

assert (L (d (DW e2))) as Hdl2.
  destruct Hwfl as [? [? [? Hldf]]]; apply Hldf; auto.
assert (L (f (DR (e,e1)))) as Hdl.
  auto.

destruct (Hmns (f (DR (e,e1))) Hdl) as [n [s0 [s1 [s2 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
simpl in Hs; unfold flush_resolved_read_step in Hs.
  
destruct (bin (Rs s1) e1); [|inversion Hs].
destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) e1 e))); [|inversion Hs];
destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) e1 e))); [|inversion Hs].

unfold visible in Hs.
destruct (is_emp (Intersection _ (B s1) (fun e => po_loc E e1 e))); [|inversion Hs].
destruct (eqEv_dec (wbef E (B s1) e1) dB); [|inversion Hs].
destruct (eqEv_dec (waft E (B s1) e1) dB); [inversion Hs|].
generalize (waft_dB E (B s1) e1); intros [dir ?]; generalize (dir e3); intro Hn.
apply Hn; exists e2; destruct H12 as [? [? ?]]; split; auto.

case_eq (bin (fun e0 : Event =>
            (phi e0 (waft E (B s1) e1) /\ loc e1 = loc e0) \/
            (po_loc E e0 e1 /\ e0 = e)) e); intros Haft; [|rewrite Haft in Hs; inversion Hs].

generalize (bin_In (fun e0 : Event =>
            (phi e0 (waft E (B s1) e1) /\ loc e1 = loc e0) \/
            (po_loc E e0 e1 /\ e0 = e)) e Haft);
intros [[Hb Heql] | [Hpo ?]].

generalize (EPick.pick_in (fun w => (B s1) w /\ loc e1 = loc w /\
                                    po_iico E e1 w /\
                                    ~ (exists w', loc e1 = loc w' /\ po_iico E e1 w' (*/\ po_iico E w' w*))));
fold (waft E (B s1) e1); intros [Hr [Hl [Hpo Hn]]].
assert (exists w', (loc e1 = loc w' /\ po_iico E e1 w')) as Hc. (*HERE*)
  exists e2; split; auto.
contradiction.

assert (po_loc_llh E e e2) as Hpoee2.
  split; [|split]; auto.
    apply ABasic.po_trans with e1; auto; destruct Hpo; auto.
    intros [Hre Hre2]. 
    destruct Hw2 as [? [? [? Hwe]]];
    destruct Hre as [? [? [? Hre]]];
    rewrite Hwe in Hre; inversion Hre.

generalize Hws'; fold (~(ws (p2X E p L) e2 e)). 
apply path_uniws with phi; auto.

destruct (bin (fun e0 : Event =>
            (e0 = wbef E (B s1) e1 \/ phi (wbef E (B s1) e1) e0) /\
            loc e1 = loc e0 (*\/
            po_loc E e0 e1 /\
            ~(exists e' : Event,
               writes E e' /\
               loc e' = loc e1 /\ po_loc E e0 e' /\ po_loc E e' e1) /\ 
            e0 = e*)) e); [|inversion Hs].
destruct (eqEv_dec (waft E (B s1) e1) dB); [inversion Hs|].
generalize (waft_dB E (B s1) e1); intros [dir ?]; generalize (dir e0); intro Hn.
apply Hn; exists e2; destruct H12 as [? [? ?]]; split; auto.

case_eq (bin (fun e0 : Event =>
            phi e0 (waft E (B s1) e1) /\ loc e1 = loc e0 \/
            po_loc E e0 e1 /\ e0 = e) e); intros Haft; [|rewrite Haft in Hs; inversion Hs].

generalize (bin_In (fun e0 : Event =>
            phi e0 (waft E (B s1) e1) /\ loc e1 = loc e0 \/
            po_loc E e0 e1 /\ e0 = e) e Haft);
intros [[Hb Heql] | [Hpo ?]].

generalize (EPick.pick_in (fun w => (B s1) w /\ loc e1 = loc w /\
                                    po_iico E e1 w /\
                                    ~ (exists w', loc e1 = loc w' /\ po_iico E e1 w')));
fold (waft E (B s1) e1); intros [Hr [Hl [Hpo Hn]]].

assert (exists w', (loc e1 = loc w' /\ po_iico E e1 w')) as Hc.
  exists e2; split; auto.
contradiction.

generalize Hws'; fold (~(ws (p2X E p L) e2 e)); apply path_uniws with phi; auto.
split; [|split]; auto.
  apply ABasic.po_trans with e1; auto; destruct Hpo; auto.
  intros [Hre Hre2]. 
  destruct Hw2 as [? [? [? Hwe]]];
  destruct Hre as [? [? [? Hre]]];
  rewrite Hwe in Hre; inversion Hre.
Qed. (*todo: make this proof better:
1. bizarre that we make the contradiction HERE over something that's not quite waft
2. the proof hasn't changed a bit when we did s/B s1/prop in the defn of visible*)

Lemma tc_ppo_fences_in_po :
  forall E e1 e2,
  well_formed_event_structure E ->
  tc (rel_union (A.ppo E) (A.fences E)) e1 e2 ->
  po_iico E e1 e2.
Proof.
intros E e1 e2 Hwf H12; induction H12; auto.
  inversion H.
    apply A.ppo_valid; auto.
    apply A.fences_valid; auto.

  apply ABasic.po_trans with z; auto.
Qed. 

Lemma hb_irr :
  forall E p L x,
  well_formed_event_structure E ->
  ~ rel_seq (tc (rel_union (A.ppo E) (A.fences E))) (rfe (p2X E p L)) x x.
Proof.
intros E p L x Hwf [e [Hxe Hex]].

generalize (tc_ppo_fences_in_po E x e Hwf Hxe); intro Hpo.
assert (events E x) as Hx.
  apply ABasic.po_iico_domain_in_events with e; auto.
assert (events E e) as He.
  apply ABasic.po_iico_range_in_events with x; auto.
generalize (ABasic.po_implies_same_proc Hwf Hx He Hpo); intro Hp.
destruct Hex as [? Hn]; apply Hn; auto. 
Qed.

Lemma co_prop_irr :
  forall E p L x phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  machine_not_stuck E p L phi ->  
  wf_labels E L -> wf_rf_labels E L ->
(*  (forall w w', loc w = loc w' -> tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  ~ rel_seq (co (p2X E p L)) (A.prop E (p2X E p L)) x x.
Proof.
intros E p L x phi Hwf Hudrp Htp Hacp Htotp Hmns Hwfl Hwfrfl (*Hfifo*) Hxx.

assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros x1 x2 x3 [H12 H23]; apply Htp with x2; auto.
    intros e He; apply Hacp with e; apply trc_step; auto.

destruct Hxx as [w [Hco Hprop]].

simpl in Hco; unfold p2ws in Hco;
destruct Hco as [Hwx [Hww [Hlxw [lx [lw [Hlx [Hlw Hp]]]]]]].

assert (L (f (DW w))) as Hlfw.
  apply Hudrp; rewrite <- Hlw; right; exists lx; auto.
generalize (Hmns (f (DW w)) Hlfw);
intros [n [s0 [s1 [s2 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_write_step in Hs.
destruct (bin ((B s1)) w); [|inversion Hs].
case_eq (bemp
            (rrestrict
               (fun w1 w2 : Event =>
                (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = w)
               (fun e : Event => udr (Rcp s1) e))); intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (bemp_axt (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ A.prop E (p2X E p L) w1 w2) /\ w1 = w) (fun e : Event => udr (Rcp s1) e) Hb); intro Hn;
apply Hn; exists x; split; auto.
  exists w; split; auto.
  rewrite Hlx in Hp; rewrite Hlw in Hp;
  apply in_order_implies_in_rcp with E p L (f (DW w)) n s0 (f (DW w)) phi; auto.
    apply dB_not_in_E with E; auto.
    destruct Hwx as [? ?]; auto.
    exists (pred p (f (DW w))); split; [|split; [|split]]; auto.
      apply td_tpred; auto.
      intros e1 e2 H12; auto.
      apply Last.no_interv_last; auto; intros e1 e2 H12; auto.
Qed.

Lemma flush_read_q_step :
  forall E (*p L*) s0 s1 de w r phi,
  reads E (evt_of_devt de) ->
  ~(Rs s0) (evt_of_devt de) -> 
  (Rs s1) (evt_of_devt de) ->
  flush_resolved_read_step E (*p L*) s0 w r phi = Some s1 ->
  f (DR (w,r)) = d de.  
Proof.
intros E (*p L*) s0 s1 de w r phi Hisr Hni0 Hi1 Hs.
    unfold flush_resolved_read_step in Hs.
      destruct (bin (Rs s0) r); [|inversion Hs];
      destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
      destruct (is_emp (Intersection _ (B s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (visible E (*p L*) s0 w r phi); [|inversion Hs].
  inversion Hs as [Heq]; rewrite <- Heq in Hi1; simpl in Hi1.
      contradiction.
Qed.

Lemma q_step :
  forall E p (L:set Label) s0 s1 lb de phi,
  (forall (w : Event), L (d (DW w)) -> writes E w) ->
  reads E (evt_of_devt de) ->
  wf_labels E L ->
  wf_rf_labels E L ->
  ~(Rs s0) (evt_of_devt de) -> 
  (Rs s1) (evt_of_devt de) ->
  L lb -> L (d de) ->
  step E p L (Some s0) lb phi = Some s1 ->
  lb = d de.
Proof.
intros E p L s0 s1 lb de phi Hwflw Hisr Hwfl Hwfr Hni0 Hi1 Hllb Hlde Hs.
case_eq lb; intros de' Hdlb.

  case_eq de'.
  intros [w r] Hde'. rewrite Hdlb in Hs; rewrite Hde' in Hs.
  
    unfold step in Hs; unfold buff_read_step in Hs.


    destruct (okw E (B s0) w r); [|inversion Hs];
    destruct (is_emp (Intersection Event (Rs s0) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
    destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) 
      (fun e => rel_seq (A.prop E (p2X E p L)) ((AWmm.hb E (p2X E p L))) e r))); [|inversion Hs].
    inversion Hs as [Heq]; rewrite <- Heq in Hi1; simpl in Hi1.
    inversion Hi1 as [e Hiq | e Hdq].
      assert ((Rs s0) (evt_of_devt de)) as Hc.
        auto.
      contradiction. 

        case_eq de.
          intros [w' r'] Hde.
            rewrite Hde in Hdq; simpl in Hdq; rewrite Hdq; auto.
            assert (L (d (DR (w,r)))) as Hldw.
              rewrite Hde' in Hdlb; rewrite Hdlb in Hllb; auto.

            assert (L (d (DR (w',r')))) as Hldw'.
              rewrite Hde in Hlde; auto.

            rewrite Hdq in Hldw'; destruct Hwfr as [? [Hwfr ?]];
            generalize (Hwfr r w w' Hldw Hldw'); intro Heqw;
            rewrite Heqw; auto.  

          intros w' Hde.
            rewrite Hde in Hlde;
            generalize (Hwflw w' Hlde); intros [? [? [? Haw]]];
            rewrite Hde in Hisr; simpl in Hisr; destruct Hisr as [? [? [? Har]]];
            rewrite Har in Haw; inversion Haw.

  intros e Hde'; rewrite Hde' in Hdlb; rewrite Hdlb in Hs;
  simpl in Hs; unfold buff_write_step in Hs.
  destruct (is_emp (Intersection Event (Rs s0) (fun r' : Event => (A.fences E) e r'))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s0) (fun e0 => po_iico E e e0 /\ loc e = loc e0))); [|inversion Hs].
  destruct (is_emp (Intersection _ (B s0) (fun e0 => (A.prop E (p2X E p L)) e e0))); [|inversion Hs].
  inversion Hs as [Heq].
    rewrite <- Heq in Hi1; simpl in Hi1; contradiction.

  case_eq de'.

  intros [w r] Hde'; rewrite Hdlb in Hs; rewrite Hde' in Hs; simpl in Hs.
  apply flush_read_q_step with E (*p L*) s0 s1 phi; auto.
  
  intros w Hde'; rewrite Hdlb in Hs; rewrite Hde' in Hs; simpl in Hs.

    unfold flush_write_step in Hs.
    destruct (bin ((B s0)) w); [|inversion Hs].
    destruct (bemp
           (rrestrict (fun w1 w2 : Event => (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\ w1 = w)
              (fun e : Event => udr (Rcp s0) e))); [|inversion Hs].
    inversion Hs as [Heqs]; rewrite <- Heqs in Hi1; simpl in Hi1; contradiction.
Qed.

Lemma p_dr_fr :
  forall E p L w r phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  L (f (DR (w,r))) ->
  p (d (DR (w, r))) (f (DR (w, r))).
Proof.
intros E p L w r phi Hwf Hwfl Hwfrfl Hlp Hmns Hlf.
assert (d (DR (w,r)) <> f (DR (w,r))) as Hdiff.
  intro Heq; inversion Heq.
destruct_lin Hlp.
assert (p (d (DR (w, r))) (f (DR (w, r))) \/ p (f (DR (w, r))) (d (DR (w, r)))) as Hor.
  apply Htot; auto.
  destruct Hwfl as [? [? [? Hfd]]]; apply Hfd; auto.
inversion Hor as [|Hfd]; clear Hor; auto.
generalize (Hmns (f (DR (w,r))) Hlf); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_resolved_read_step in Hs.
case_eq (bin (Rs s1) r); intro Hi; rewrite Hi in Hs; [|inversion Hs].
assert (trans p) as Htp.
  intros x y z Hxy Hyz; apply Htrans with y; auto.
rewrite <- trans_tc with Label p; auto.
apply in_rs_implies_d_before with E L n s0 s1 r phi; auto.
  rewrite trans_tc; auto.
  generalize (bin_In (Rs s1) r Hi); intro Hir.
    destruct (Hwfrs r Hir); auto.
  intros x y z Hxy Hyx; apply trc_ind with y; auto.
  generalize (bin_In (Rs s1) r Hi); intro Hir; generalize (Hwfrs r Hir); intros [? ?]; auto.
  destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.
  apply bin_In; auto.
  exists (pred p (f (DR (w,r)))); split; [|split; [|split]]; auto.
    apply td_tpred; auto.
    intros x y Hxy; auto.
    rewrite trans_tc; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.
      apply trc_step; auto.
Qed. 

Lemma ci0_rr_f_d :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  (*wf_l_p E p L ->*)
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  (forall w1 r1 w2 r2, L (f (DR (w1, r1))) -> L (d (DR (w2, r2))) ->
   tc (rel_union (A.ppo E) (A.fences E)) (evt_of_devt (DR (w1,r1))) (evt_of_devt (DR (w2,r2))) -> 
   p (f (DR (w1,r1))) (d (DR (w2,r2)))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl (*Hwflp*) Hlp Hmns w1 r1 w2 r2 Hl1 Hl2 H12.
assert (f (DR (w1,r1)) <> d (DR (w2,r2))) as Hdiff.
  intro Heq; inversion Heq; rewrite H1 in H12.
assert (p (f (DR (w1,r1))) (d (DR (w2,r2))) \/ p (d (DR (w2,r2))) (f (DR (w1,r1)))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [|H21]; clear Hor; auto.
  generalize (Hmns (f (DR (w1,r1))) Hl1); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]];
  unfold step in Hs; unfold flush_resolved_read_step in Hs.
  destruct (bin (Rs s1) r1); [|inversion Hs].
  case_eq (is_emp
           (Intersection Event (Rs s1)
              (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e)));
  intro Hemp; rewrite Hemp in Hs; [|inversion Hs]; auto.
  generalize (is_emp_axt (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e) Hemp);
  intro Hn.

  assert (exists e : Event, Rs s1 e /\ tc (rel_union (A.ppo E) (A.fences E)) r1 e) as Hy.
    exists r2; split; auto.
      assert (trans p) as Htp.
        destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
      destruct_lin Hlp; apply in_order_implies_in_rs with E p L (f (DR (w1,r1))) n s0 (f (DR (w1,r1))) w2 phi; auto.
        intros x Hx; apply Hac with x; rewrite trans_tc in Hx; auto.
        exists (pred p (f (DR (w1,r1)))); split; [|split; [|split]]; auto.
          apply td_tpred; auto.
          intros x y Hxy; auto.
          apply Last.no_interv_last; auto; intros x y Hxy; auto.
  contradiction.
Qed.

Lemma fenceWR_d_d :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  (*wf_l_p E p L ->*)
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->  
  (forall w1 w2 r2, L (d (DW w1)) -> L (d (DR (w2,r2))) -> 
    (A.fences E) w1 r2 -> p (d (DW w1)) (d (DR (w2,r2)))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl (*Hwflp*) Hlp Hmns w1 w2 r2 Hl1 Hl2 H12.
assert (d (DW w1) <> d (DR (w2,r2))) as Hdiff.
  intro Heq; inversion Heq; rewrite H1 in H12.
assert (p (d (DW w1)) (d (DR (w2,r2))) \/ p (d (DR (w2,r2))) (d (DW w1))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [|H21]; clear Hor; auto.
generalize (Hmns (d (DW w1)) Hl1); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]];
unfold step in Hs; unfold buff_write_step in Hs.
case_eq (is_emp (Intersection Event (Rs s1) (fun r' : Event => A.fences E w1 r'))); intro Hr;
rewrite Hr in Hs; [|inversion Hs].

generalize (is_emp_axt (Rs s1) (fun r' : Event => A.fences E w1 r') Hr); intro Hn.
assert (exists e : Event, Rs s1 e /\ A.fences E w1 e) as Hy.
  exists r2; split; auto.
    assert (trans p) as Htp.
      destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
    destruct_lin Hlp;
    apply in_order_implies_in_rs with E p L (d (DW w1)) n s0 (d (DW w1)) w2 phi; auto.
    intros x; rewrite trans_tc; auto; apply Hac; auto. 
    exists (pred p (d (DW w1))); split; [|split; [|split]]; auto.
      apply td_tpred; auto.
      intros x y Hxy; auto.
      apply Last.no_interv_last; auto; intros x y Hxy; auto.
contradiction.
Qed. 

Lemma hb_irr' :
  forall E p L x,
  well_formed_event_structure E ->
  ~(AWmm.hb E (p2X E p L) x x).
Proof.
intros E p L x Hwf [[Hx Hp] |Hx].
  apply Hp; auto.
  generalize (tc_ppo_fences_in_po E x x Hwf Hx); intro Hpo.
  apply (ABasic.po_ac Hwf Hpo).
Qed.

Lemma rfe_d_d :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  (*wf_l_p E p L ->*)
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  (forall w1 w2 r2, L (d (DW w1)) -> L (d (DR (w2,r2))) -> 
   rfe (p2X E p L) w1 r2 -> p (d (DW w1)) (d (DR (w2,r2)))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl (*Hwflp*) Hlp Hmns w1 w2 r2 Hl1 Hl2 H12.
assert (d (DW w1) <> d (DR (w2,r2))) as Hdiff.
  intro Heq; inversion Heq as [Heqd]; rewrite Heqd in H12.

assert (p (d (DW w1)) (d (DR (w2,r2))) \/ p (d (DR (w2,r2))) (d (DW w1))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [|H21]; clear Hor; auto.
assert (L (d (DR (w2,r2)))) as Hldr2.
  destruct_lin Hlp; apply Hdr; left; exists (d (DW w1)); auto.
generalize (Hmns (d (DR (w2,r2))) Hldr2); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]];
unfold step in Hs; unfold buff_read_step in Hs.
case_eq (okw E (B s1) w2 r2); intro Hok; rewrite Hok in Hs; [|inversion Hs].
assert (proc_of w2 = proc_of r2 \/ (B s1) w2) as Hok'.
  generalize (okw_ext E (B s1) w2 r2 Hwf Hok); intros [[? Hpo] | Hb].
    left; apply ABasic.po_implies_same_proc with E; auto.
    apply ABasic.po_iico_domain_in_events with r2; auto.
    apply ABasic.po_iico_range_in_events with w2; auto.
  right; auto.

assert (rfmaps_well_formed E (events E) (rf (p2X E p L))) as Hrfwf.
  generalize (path_rf_wf E p L Hlp Hwfrfl); auto.

generalize H12; intros H12'; destruct H12' as [[? Hlf] ?].
destruct Hwfl as [? [? [Hwl Hdf]]].
generalize (Hdf (DR (w1, r2)) Hlf); intro Hld.
destruct Hwfrfl as [? [Hldeq ?]].
generalize (Hldeq r2 w2 w1 Hldr2 Hld); intro Heq.

assert (writes E w1) as Hw1.
  destruct H12 as [Hrf ?]; simpl; split; auto.
  apply ABasic.dom_rf_in_events with (p2X E p L) r2; auto.
  apply ABasic.dom_rf_is_write with E (p2X E p L) r2; auto.   
    destruct Hrfwf as [? [? ?]]; auto.
generalize (Hwl w1 Hw1); intro Hlde1.
assert (w1 = w2) as Heqw.
  apply Hldeq with r2; auto.

inversion Hok' as [Hp | Hb]; clear Hok'.
  destruct H12 as [? Hnp].
    rewrite Heqw in Hnp; simpl in Hnp. 
    assert False as Ht.
      apply Hnp; auto.
    inversion Ht.
  assert (trans p) as Htp. 
    destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
  assert (events E w2) as Hew2.
    rewrite <- Heq in H; destruct H as [? [? ?]]; auto.
  assert (exists dr : Rln Label,
    trans dr /\
    rel_incl dr (pred p (d (DR (w2,r2)))) /\
    (~ (exists l' : Label, tc p (Last.last dr) l' /\ tc p l' (d (DR (w2,r2)))) \/
     Last.last dr = (d (DR (w2,r2)))) /\ machine E dr L (d (DR (w2,r2))) n phi (Some s0) (Some s1)) as Hex.
  exists (pred p (d (DR (w2,r2)))); split; [|split; [|split]]; auto.
    apply td_tpred; auto. intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto.  intros x y Hxy; auto.
  
  generalize (in_buff_implies_before E p L (d (DR (w2,r2))) n s0 s1 w2 phi Htp Hew2 Hb Hex).
  rewrite Heqw; auto. 
Qed.

Lemma cc0rw_f_d :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  (*wf_l_p E p L ->*)
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  (forall wr r w, L (f (DR (wr,r))) -> L (d (DW w)) ->
   tc (rel_union (A.ppo E) (A.fences E)) (evt_of_devt (DR (wr,r))) (evt_of_devt (DW w)) -> 
   p (f (DR (wr,r))) (d (DW w))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hlp Hmns wr r w Hlr Hlw H12.
assert (f (DR (wr,r)) <> d (DW w)) as Hdiff.
  intro Heq; inversion Heq as [Heqd]; rewrite Heqd in H12.
assert (p (f (DR (wr,r))) (d (DW w)) \/ p (d (DW w)) (f (DR (wr,r)))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [|H21]; clear Hor; auto.
  generalize (Hmns (f (DR (wr,r))) Hlr); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]];
  unfold step in Hs; unfold flush_resolved_read_step in Hs.
  destruct (bin (Rs s1) r); [|inversion Hs].
  destruct (is_emp
           (Intersection Event (Rs s1)
              (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  case_eq (is_emp
           (Intersection _ (B s1)
              (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e)));
  intro Hemp; rewrite Hemp in Hs; [|inversion Hs].
  generalize (is_emp_axt (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e) Hemp); intro Hn.
  assert (exists e : Event, (B s1) e /\ tc (rel_union (A.ppo E) (A.fences E)) r e) as Hy.
    exists w; split; auto.
      assert (trans p) as Htp.
        destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
      destruct_lin Hlp; (*exists dB;*) apply in_order_implies_in_buff with E p L (f (DR (wr,r))) n s0 (f (DR (wr,r))) phi; auto.
        intros x Hx; apply Hac with x; rewrite trans_tc in Hx; auto.
        apply wfl_e; auto.
        apply if_ldw_then_lfw with E; auto.
        exists (pred p (f (DR (wr,r)))); split; [|split; [|split]]; auto.
          apply td_tpred; auto.
          intros x y Hxy; auto.
          left; apply Last.no_interv_last; auto; intros x y Hxy; auto.
  contradiction.
Qed. 

Lemma prop_d_d :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  (*wf_l_p E p L ->*)
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->  
  (forall w1 w2, L (d (DW w1)) -> L (d (DW w2)) -> 
    (A.prop E (p2X E p L)) w1 w2 -> p (d (DW w1)) (d (DW w2))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hlp Hmns w1 w2 Hlde1 Hlde2 H12.
assert (d (DW w1) <> d (DW w2)) as Hdiff.
  intro Heq; inversion Heq as [Hde]; rewrite Hde in H12. 
  assert (exists x, A.prop E (p2X E p L) x x) as Hex.
    exists w2; auto.
  apply (A.prop_valid E (p2X E p L) Hex). 
assert (p (d (DW w1)) (d (DW w2)) \/ p (d (DW w2)) (d (DW w1))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [|H21]; clear Hor; auto.
generalize (Hmns (d (DW w1)) Hlde1); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold buff_write_step in Hs.
destruct (is_emp
           (Intersection Event (Rs s1)
              (fun r' : Event => (A.fences E) w1 r'))); [|inversion Hs].
destruct (is_emp (Intersection _ (B s1) (fun e : Event =>po_iico E w1 e /\ loc w1 = loc e))); [|inversion Hs].
case_eq (is_emp (Intersection _ (B s1) (fun e : Event => A.prop E (p2X E p L) w1 e))); intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (is_emp_axt (B s1) (fun e : Event => A.prop E (p2X E p L) w1 e) Hb); intro Hn.
assert (exists e : Event, (B s1) e /\ A.prop E (p2X E p L) w1 e) as Hy.
  exists w2; split; auto.
  assert (trans p) as Htp.
    destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
  destruct_lin Hlp; apply in_order_implies_in_buff with E p L (d (DW w1)) n s0 (d (DW w1)) phi; auto.
    intros x Hx; apply Hac with x; auto; rewrite <- trans_tc with Label p; auto.
    apply wfl_e; auto. 
    apply if_ldw_then_lfw with E; auto; apply Hdr; left; exists (d (DW w1)); auto.    
    exists (pred p (d (DW w1))); split; [|split; [|split]]; auto.
      apply td_tpred; auto. intros x y Hxy; auto.
      left; apply Last.no_interv_last; auto.
      intros x y Hxy; auto.
contradiction.
Qed.

Hypothesis dom_prop_W :
  forall E X x y,
  tc (A.prop E X) x y ->
  writes E x.
Hypothesis ran_prop_W :
  forall E X x y,
  tc (A.prop E X) x y ->
  writes E y.
Lemma prop_f_f :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  (*wf_l_p E p L ->*)
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->  
  (forall w1 w2, L (f (DW w1)) -> L (f (DW w2)) -> 
    (A.prop E (p2X E p L)) w1 w2 -> p (f (DW w1)) (f (DW w2))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hlp Hmns w1 w2 Hlfe1 Hlfe2 H12.
assert (f (DW w1) <> f (DW w2)) as Hdiff.
  intro Heq; inversion Heq as [Hde]; rewrite Hde in H12. 
  assert (exists x, A.prop E (p2X E p L) x x) as Hex.
    exists w2; auto.
  apply (A.prop_valid E (p2X E p L) Hex). 
assert (p (f (DW w1)) (f (DW w2)) \/ p (f (DW w2)) (f (DW w1))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [|H21]; clear Hor; auto.

generalize (Hmns (f (DW w1)) Hlfe1).
intros [n [s0 [s1 [s2 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_write_step in Hs.
destruct (bin (B s1) w1); [|inversion Hs].
case_eq (bemp (rrestrict (fun w2 w3 : Event => (po_loc E w2 w3 \/ (A.prop E (p2X E p L)) w2 w3) /\ w2 = w1)
              (fun e : Event => udr (Rcp s1) e))); 
intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (bemp_axt (fun w2 w3 : Event => (po_loc E w2 w3 \/ (A.prop E (p2X E p L)) w2 w3) /\ w2 = w1) (fun e : Event => udr (Rcp s1) e) Hb);
intro Hn.
destruct_lin Hlp.
assert (trans p) as Htp.
  intros x y z Hxy Hyz; apply Htrans with y; auto.
assert (acyclic p) as Hacp.
  intros x Hx. rewrite trans_tc with Label p in Hx; auto. apply (Hac x Hx).
assert (exists e : Event,
        ran (fun w2 w3 : Event => (po_loc E w2 w3 \/ (A.prop E (p2X E p L)) w2 w3) /\ w2 = w1) e /\ udr (Rcp s1) e) as Hy.
exists w2; split; auto.
  exists w1; split; auto.

  apply in_order_implies_in_rcp with E p L (f (DW w1)) n s0 (f (DW w1)) phi; auto.
  apply dB_not_in_E with E; auto.
    assert (tc (A.prop E (p2X E p L)) w1 w2) as Htc.
      apply trc_step; auto.
    generalize (ran_prop_W E (p2X E p L) w1 w2 Htc); intros [? ?]; auto.
  
  exists (pred p (f (DW w1))); split; [|split; [|split]]; auto.
    apply td_tpred; auto.
    intros e1 e2 He12; auto.
    apply Last.no_interv_last; auto.
      intros e1 e2 He12; auto.

contradiction.
Qed.

Definition wf_devts E :=
  (forall de, writes E (evt_of_devt de) -> exists w, de = DW w) /\
  (forall de, reads E (evt_of_devt de) -> exists w, exists r, de = DR (w,r)).

Lemma rf_dom_label :
  forall E X L de1 de2,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  wf_labels E L -> wf_rf_labels E L -> wf_devts E ->
  rf X (evt_of_devt de1) (evt_of_devt de2) ->
  exists w1, de1 = DW w1.
Proof.
intros E X L de1 de2 Hwf Hrfwf Hwfl [Hex ?] [Hwfdw ?] Hrf.
assert (writes E (evt_of_devt de1)) as Hw1.
  split. 
    apply ABasic.dom_rf_in_events with X (evt_of_devt de2); auto.
    apply ABasic.dom_rf_is_write with E X (evt_of_devt de2); auto.
      destruct Hrfwf as [? [? ?]]; auto.
apply Hwfdw; auto.
Qed.

Lemma rf_ran_label :
  forall E X L de1 de2,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  wf_labels E L -> wf_rf_labels E L -> wf_devts E ->
  rf X (evt_of_devt de1) (evt_of_devt de2) ->
  exists w2, exists r2, de2 = DR (w2,r2).
Proof.
intros E X L de1 de2 Hwf Hrfwf Hwfl [Hex ?] [? Hwfdr] Hrf.
assert (reads E (evt_of_devt de2)) as Hr2.
  split. 
    apply ABasic.ran_rf_in_events with X (evt_of_devt de1); auto.
    apply ABasic.ran_rf_is_read with E X (evt_of_devt de1); auto.
      destruct Hrfwf as [? [? ?]]; auto.
apply Hwfdr; auto.
Qed.

Hypothesis ppof_WW_prop :
  (*ppo starts with R hence Hppof => fenceWW which is in prop*)
  forall E X w1 w2,
  tc (rel_union (A.ppo E) (A.fences E)) w1 w2 ->
  A.prop E X w1 w2.

Hypothesis ppof_WR_fence :
  (*ppo starts with R hence Hppof => fenceWR*)
  forall E w r,
  tc (rel_union (A.ppo E) (A.fences E)) w r ->
  A.fences E w r.

Lemma hb_d_d :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L -> wf_devts E ->
  (*wf_l_p E p L ->*)
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  (forall de1 de2, L (d de1) -> L (d de2) ->
   AWmm.hb E (p2X E p L) (evt_of_devt de1) (evt_of_devt de2) -> p (d de1) (d de2)).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hwfd Hlp Hmns de1 de2 Hl1 Hl2 H12.
assert (d de1 <> d de2) as Hdiff.
  intro Heq; inversion Heq as [Heqd]; rewrite Heqd in H12.
  generalize H12; apply hb_irr'; auto.
assert (p (d de1) (d de2) \/ p (d de2) (d de1)) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [|H21]; clear Hor; auto.
inversion H12 as [Hrf | Hppof].
  assert (exists w2, exists r2, de2 = DR (w2,r2)) as Hw2r2.
    apply rf_ran_label with E (p2X E p L) L de1; auto.
    apply path_rf_wf; auto.
    destruct Hrf; auto.
  assert (exists w1, de1 = DW w1) as Hw1.
    apply rf_dom_label with E (p2X E p L) L de2; auto.
    apply path_rf_wf; auto.
    destruct Hrf; auto.
  destruct Hw2r2 as [w2 [r2 Hr2]]; rewrite Hr2; destruct Hw1 as [w1 Hw1]; rewrite Hw1;
  apply rfe_d_d with E L phi; auto.
  rewrite <- Hw1; auto.
  rewrite <- Hr2; auto. 
  rewrite Hr2 in Hrf; simpl in Hrf; auto.
  rewrite Hw1 in Hrf; auto.
  case_eq (action (evt_of_devt de1)); intros drn l v Ha1; case_eq drn; intros Hdrn; rewrite Hdrn in Ha1.
    assert (reads E (evt_of_devt de1)) as Hisr1.
      split; auto.
        apply ABasic.po_iico_domain_in_events with (evt_of_devt de2); auto.
        apply tc_ppo_fences_in_po; auto.
        exists l; exists v; auto.
    assert (exists w1, exists r1, de1 = DR (w1,r1)) as Hw1r1.
      destruct Hwfd as [? Hwfdr]; apply Hwfdr; auto.
    destruct Hw1r1 as [w1 [r1 Hr1]]; rewrite Hr1.
    assert (L (f (DR (w1,r1)))) as Hlf1.
      rewrite Hr1 in Hl1; apply if_ldr_then_lfr with E; auto.
    generalize Hlp; intro Hlp'; destruct_lin Hlp; apply Htrans with (f (DR (w1,r1))); split; auto. 
      apply p_dr_fr with E L phi; auto. 
      case_eq (action (evt_of_devt de2)); intros drn2 l2 v2 Ha2; case_eq drn2; intros Hdrn2; rewrite Hdrn2 in Ha2.
      assert (reads E (evt_of_devt de2)) as Hisr2.
      split; auto.
        apply ABasic.po_iico_range_in_events with (evt_of_devt de1); auto.
        apply tc_ppo_fences_in_po; auto.
        exists l2; exists v2; auto.
      assert (exists w2, exists r2, de2 = DR (w2,r2)) as Hw2r2.
        destruct Hwfd as [? Hwfdr]; apply Hwfdr; auto.
      destruct Hw2r2 as [w2 [r2 Hr2]]; rewrite Hr2.
      apply ci0_rr_f_d with E L phi; auto.
        rewrite <- Hr2; auto.
        rewrite Hr1 in Hppof; rewrite Hr2 in Hppof; simpl in Hppof; auto.
      assert (writes E (evt_of_devt de2)) as Hisw2.
      split; auto.
        apply ABasic.po_iico_range_in_events with (evt_of_devt de1); auto.
        apply tc_ppo_fences_in_po; auto.
        exists l2; exists v2; auto.
      assert (exists w2, de2 = DW w2) as Hw2.
        destruct Hwfd as [Hwfdw ?]; apply Hwfdw; auto.
      destruct Hw2 as [w2 Hw2]; rewrite Hw2.
      apply cc0rw_f_d with E L phi; auto.
        rewrite <- Hw2; auto.
        rewrite Hr1 in Hppof; rewrite Hw2 in Hppof; simpl in Hppof; auto.

      assert (writes E (evt_of_devt de1)) as Hisw1.
      split; auto.
        apply ABasic.po_iico_domain_in_events with (evt_of_devt de2); auto.
        apply tc_ppo_fences_in_po; auto.
        exists l; exists v; auto.
    assert (exists w1, de1 = DW w1) as Hw1.
        destruct Hwfd as [Hwfdw ?]; apply Hwfdw; auto.
    destruct Hw1 as [w1 Hw1].
    assert (events E (evt_of_devt de2)) as Hede2.
        apply ABasic.po_iico_range_in_events with (evt_of_devt de1); auto.
        apply tc_ppo_fences_in_po; auto.      
    assert (writes E (evt_of_devt de2) \/ reads E (evt_of_devt de2)) as Hwr.
      case_eq (action (evt_of_devt de2)); intros drn2 l2 v2 Ha2; case_eq drn2; intro Hdrn2; rewrite Hdrn2 in Ha2.
        right; split; auto; exists l2; exists v2; auto.
        left; split; auto; exists l2; exists v2; auto.
    assert ((exists w2, de2 = DW w2) \/ (exists w2, exists r2, de2 = DR (w2,r2))) as Hor.
      destruct Hwfd as [Hwfdw Hwfdr]; inversion Hwr as [Hw | Hr].
        left; apply Hwfdw; auto. right; apply Hwfdr; auto.
    inversion Hor as [[w2 Hw2] | [w2 [r2 Hr2]]]; clear Hor; rewrite Hw1 in Hppof; rewrite Hw1.
      rewrite Hw2 in Hppof; rewrite Hw2.
      apply prop_d_d with E L phi; auto.
        rewrite <- Hw1; auto. rewrite <- Hw2; auto.
        apply ppof_WW_prop; auto.
      
      rewrite Hr2 in Hppof; rewrite Hr2.

      apply fenceWR_d_d with E L phi; auto. 
        rewrite <- Hw1; auto. rewrite <- Hr2; auto.
        apply ppof_WR_fence; auto. 
Qed.            
 
Lemma hb_implies_p :
  forall E p L w1 w2 r1 r2 phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->
  (forall w1 r1 de2, L (d (DR (w1,r1))) -> L (d de2) -> (AWmm.hb E (p2X E p L)) r1 (evt_of_devt de2) -> p (d (DR (w1,r1))) (d de2)) ->
  machine_not_stuck E p L phi -> 
  wf_labels E L -> wf_rf_labels E L -> wf_devts E -> 
  L (f (DR (w1,r1))) -> L (f (DR (w2,r2))) ->
  (rel_seq (tc (rel_union (A.ppo E) (A.fences E))) (rfe (p2X E p L))) r1 r2 -> 
  p (d (DR (w1,r1))) (d (DR (w2,r2))).
Proof.
intros E p L w1 w2 r1 r2 phi Hwf Hudrp Htp Hacp Htotp Hphb Hmns Hwfl Hwfrfl Hwfd Hll1 Hll2 H12.
generalize H12; intros [w [Hdp1 Hrf2]].
assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros e1 e2 e3 [He12 He23]; apply Htp with e2; auto.
    intros e He; apply Hacp with e; apply trc_step; auto.

assert (L (d (DR (w2,r2)))) as Hld2.
  destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.
assert (L (d (DR (w1,r1)))) as Hld1.
  destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.
assert ((d (DR (w1,r1))) <> (d (DR (w2,r2)))) as Hdiff.
  intro Heq; inversion Heq; subst.
    generalize H12; apply hb_irr; auto.

generalize (Hmns (d (DR (w2,r2))) Hld2).
intros [n [s0 [s1 [s2 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
simpl in Hs; unfold buff_read_step in Hs.
case_eq (okw E (B s1) w2 r2); intro Hok; rewrite Hok in Hs; [|inversion Hs].
assert (w = w2) as Heqw.
  destruct Hrf2 as [[? Hlf] ?].
  destruct Hwfrfl as [? [Heqw ?]].
    apply Heqw with r2; auto.
    destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.
generalize (okw_ext E (B s1) w2 r2 Hwf Hok); intros [[? Hpo] | Hb].
  destruct Hrf2 as [? Hnp].
  assert False as Ht.
    apply Hnp; rewrite Heqw; auto.
    apply ABasic.po_implies_same_proc with E; auto. 
    apply ABasic.po_iico_domain_in_events with r2; auto.
    apply ABasic.po_iico_range_in_events with w2; auto.
  inversion Ht.
  assert (L (d (DW w2))) as Hldw2.
    destruct Hwfl as [? [? [Hlw Hdf]]].
    apply Hdf; apply Hlw; auto.
    assert (rfmaps_well_formed E (events E) (rf (p2X E p L))) as Hrfwf.
      apply path_rf_wf; auto.
    (*destruct Hrf2 as [? ?]; rewrite <- Heqw; split.
      apply ABasic.dom_rf_in_events with (p2X E p L) r2; auto.
      apply ABasic.dom_rf_is_write with E (p2X E p L) r2; auto.
        destruct Hrfwf as [? [? ?]]; auto.*)
  apply Htp with (d (DW w2)).
    apply hb_d_d with E L phi; auto.
      right; simpl; rewrite <- Heqw; auto.
    apply hb_d_d with E L phi; auto. 
      left; simpl; rewrite <- Heqw; auto.
Qed.

Lemma co_prop_implies_p :
  forall E p L w1 w2 phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->
  machine_not_stuck E p L phi -> wf_labels E L -> wf_rf_labels E L -> 
  L (f (DW w1)) -> L (f (DW w2)) -> 
  (rel_seq (co (p2X E p L)) (A.prop E (p2X E p L))) w1 w2 -> 
(*  (forall w w', loc w = loc w' -> tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  p (f (DW w1)) (f (DW w2)).
Proof.
intros E p L w1 w2 phi Hwf Hudrp Htp Hacp Htotp Hmns Hwfl Hwfrfl Hll1 Hll2 H12 (*Hfifo*).
generalize H12; intros [w [Hco1 Hprop2]].
assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros e1 e2 e3 [He12 He23]; apply Htp with e2; auto.
    intros e He; apply Hacp with e; apply trc_step; auto.

apply Htp with (f (DW w)); auto.
  destruct Hco1 as [? [? [? [lw1 [lw [Heqw1 [Heqw Hw1w]]]]]]];
  rewrite <- Heqw1; rewrite <- Heqw; auto.

assert ((f (DW w)) <> (f (DW w2))) as Hdiff.
  intro Heq; inversion Heq; subst.
    apply (A.prop_valid E (p2X E p L)); exists w2; auto.
assert (L (f (DW w))) as Hllw.
    destruct Hco1 as [? [? [? [lw1 [lw [Hlw1 [Hlw Hp]]]]]]]; auto.
  rewrite <- Hlw; auto; apply Hudrp; right; exists lw1; auto.
generalize (Htotp (f (DW w)) (f (DW w2)) Hdiff Hllw Hll2); intro Hor; 
  inversion Hor as [|H21]; clear Hor; auto.

  assert (L (d (DW w))) as Hldw.
    destruct Hco1 as [? [? [? [lw1 [lw [Hlw1 [Hlw Hp]]]]]]].
      destruct Hwfl as [? [? [? Hfd]]]; apply Hfd; auto.
  assert (L (d (DW w2))) as Hldw2.
    destruct Hwfl as [? [? [? Hfd]]]; apply Hfd; auto.    
  generalize (prop_d_d E p L phi Hwf Hwfl Hwfrfl Hlp Hmns w w2 Hldw Hldw2 Hprop2); intro Hdww2; auto.
(*todo: below is the code for prop_f_f/we can call the lemma now*)
assert (L (f (DW w1))) as Hl.
    destruct Hco1 as [? [? [? [lw1 [lw [Hlw1 [Hlw Hp]]]]]]]; auto.

generalize (Hmns (f (DW w)) Hllw).
intros [n [s0 [s1 [s2 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_write_step in Hs.
destruct (bin ((B s1)) w); [|inversion Hs].
case_eq (bemp (rrestrict (fun w2 w3 : Event => (po_loc E w2 w3 \/ (A.prop E (p2X E p L)) w2 w3) /\ w2 = w)
              (fun e : Event => udr (Rcp s1) e))); 
intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (bemp_axt (fun w2 w3 : Event => (po_loc E w2 w3 \/ (A.prop E (p2X E p L)) w2 w3) /\ w2 = w) (fun e : Event => udr (Rcp s1) e) Hb);
intro Hn.
assert (exists e : Event,
        ran (fun w2 w3 : Event => (po_loc E w2 w3 \/ (A.prop E (p2X E p L)) w2 w3) /\ w2 = w) e /\ udr (Rcp s1) e) as Hy.
exists w2; split; auto.
  exists w; split; auto.

  apply in_order_implies_in_rcp with E p L (f (DW w)) n s0 (f (DW w)) phi; auto.
  apply dB_not_in_E with E; auto.
    assert (tc (A.prop E (p2X E p L)) w w2) as Htc.
      apply trc_step; auto.
    generalize (ran_prop_W E (p2X E p L) w w2 Htc); intros [? ?]; auto.
  
  exists (pred p (f (DW w))); split; [|split; [|split]]; auto.
    apply td_tpred; auto.
    intros e1 e2 He12; auto.
    apply Last.no_interv_last; auto.
      intros e1 e2 He12; auto.

contradiction.
Qed.

Lemma tc_hb_implies_in_tc_p :
  forall E p L w1 w2 r1 r2 phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  (forall w1 r1 de2, L (d (DR (w1,r1))) -> L (d de2) -> (AWmm.hb E (p2X E p L)) r1 (evt_of_devt de2) -> p (d (DR (w1,r1))) (d de2)) ->
  machine_not_stuck E p L phi -> wf_labels E L ->
  wf_rf_labels E L -> wf_devts E ->  
  L (f (DR (w1,r1))) -> L (f (DR (w2,r2))) ->
  (evt_of_devt (DR (w1,r1))) = r1 -> 
  (evt_of_devt (DR (w2,r2))) = r2 ->
  tc (rel_seq (tc (rel_union (A.ppo E) (A.fences E))) (rfe (p2X E p L))) r1 r2 -> 
  tc p (d (DR (w1,r1))) (d (DR (w2,r2))).
Proof.
intros E p L w1 w2 r1 r2 phi Hwf Hudrp Htp Hacp Htotp Hphb Hmns Hwfl Hwfrfl Hwfd Hl1 Hl2 H1 H2 H12.
assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros e1 e2 e3 [He12 He23]; apply Htp with e2; auto.
    intros x Hx; apply Hacp with x; apply trc_step; auto.
generalize w1 w2 H1 H2 Hl1 Hl2; clear w1 w2 H1 H2 Hl1 Hl2; 
induction H12 as [x y Hs |]. 
  intros wx wy Hx Hxy Hlx Hly; apply trc_step.
     apply hb_implies_p with E L phi; auto.

  intros wx wy Hx Hy Hlx Hly.
  assert (reads E z) as Hrz.
    clear Hly Hlx y H12_0 IHtc1 IHtc2 Hx Hy.
    induction H12_; auto.
      destruct H as [w [Hdp Hrf]].
        split.
          apply ABasic.ran_rf_in_events with (p2X E p L) w; auto.
            apply path_rf_wf; auto; apply wfl_implies_wfr; auto.
            destruct Hrf; auto.
          apply ABasic.ran_rf_is_read with E (p2X E p L) w; auto.
            generalize (path_rf_wf E p L); intros [? [? ?]]; auto.
            destruct Hrf; auto.

  generalize (path_rf_wf E p L); auto; intros [Hrf_ex ?]; auto.
  generalize (Hrf_ex z Hrz); intros [wz [Hlwz [? ?]]].
  assert (evt_of_devt (DR (wz,z)) = z) as Hz.
    simpl; auto.
  apply trc_ind with (d (DR (wz,z))); [apply IHtc1 | apply IHtc2]; auto.
Qed.

Lemma dom_tc_co_in_L :
  forall E p L x y,
  Included Label (Union Label (dom p) (ran p)) L ->
  tc (rel_seq (co (p2X E p L)) (A.prop E (p2X E p L))) x y ->
  L (f (DW x)).
Proof.
intros E p L x y Hudrp Hxy.
induction Hxy; auto.
destruct H as [? [Hco ?]]; 
destruct Hco as [? [? [? [l1 [l2 [Hl1 [Hl2 Hp]]]]]]]; rewrite <- Hl1; 
apply Hudrp; left; exists l2; auto.
Qed.

Lemma tc_co_prop_implies_tc_p :
  forall E p L w1 w2 phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->
(*  (forall w w' : Event, loc w = loc w' -> tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  machine_not_stuck E p L phi -> wf_labels E L -> wf_rf_labels E L -> 
  L (f (DW w1)) -> L (f (DW w2)) ->
  tc (rel_seq (co (p2X E p L)) (A.prop E (p2X E p L))) w1 w2 -> 
  tc p (f (DW w1)) (f (DW w2)).
Proof.
intros E p L w1 w2 phi Hwf Hudrp Htp Hacp Htotp (*Hfifo*) Hmns Hwfl Hwfrfl Hl1 Hl2 H12.
assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros e1 e2 e3 [He12 He23]; apply Htp with e2; auto.
    intros x Hx; apply Hacp with x; apply trc_step; auto.
generalize Hl1 Hl2; clear Hl1 Hl2; 
induction H12 as [x y Hs |]. 
  intros Hlx Hly; apply trc_step.
     apply co_prop_implies_p with E L phi; auto.

  intros Hlx Hly.
  assert (L (f (DW z))) as Hlz.
    apply dom_tc_co_in_L with E p y; auto.

  apply trc_ind with (f (DW z)); [apply IHtc1 | apply IHtc2]; auto.
Qed.

Lemma dom_tc_rf :
  forall E X x y, 
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  tc (rel_seq (tc (rel_union (A.ppo E) (A.fences E))) (rf X)) x y ->
  reads E y.
Proof.
intros E X x y Hwf Hrfwf Hxy.
induction Hxy; auto.
  destruct H as [z [? Hrf]].
    split. 
      apply ABasic.ran_rf_in_events with X z; auto.
      apply ABasic.ran_rf_is_read with E X z; auto.
        destruct Hrfwf as [? [? ?]]; auto.
Qed.

Lemma path_hb :
  forall E p L phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  (forall w1 r1 de2, L (d (DR (w1,r1))) -> L (d de2) -> (AWmm.hb E (p2X E p L)) r1 (evt_of_devt de2) -> p (d (DR (w1,r1))) (d de2)) ->
  machine_not_stuck E p L phi -> wf_labels E L -> wf_rf_labels E L -> wf_devts E -> 
  (forall e1 e2, 
     rel_seq (tc (rel_union (A.ppo E) (A.fences E))) (rfe (p2X E p L)) e1 e2 -> 
     ~ (tc (rel_seq (tc (rel_union (A.ppo E) (A.fences E))) (rfe (p2X E p L)))) e2 e1).
Proof.
intros E p L phi Hwf Hudrp Htp Hacp Htotp Hphb Hmns Hwfl Hwfrfl Hwfd e1 e2 H12 H21.
assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros x1 x2 x3 [Hx12 Hx23]; apply Htp with x2; auto.
    intros x Hx; apply Hacp with x; apply trc_step; auto.
generalize H12; intros [w' [Hrf Hdp]].
assert (reads E e1) as Hr1.
  apply dom_tc_rf with (p2X E p L) e2; auto.
  apply path_rf_wf; auto. 
  generalize H21; apply tc_incl; intros x y [z [Hxz [Hzy ?]]]; exists z; split; auto.
assert (exists w1, L (f (DR (w1,e1)))) as Hw1.
  generalize (path_rf_wf E p L); intros [Hrf_ex ?]; auto.
  generalize (Hrf_ex e1 Hr1); intros [w1 [? [? ?]]]; exists w1; auto.
assert (reads E e2) as Hr2.
  split.
    apply ABasic.ran_rf_in_events with (p2X E p L) w'; auto.
      apply path_rf_wf; auto; apply wfl_implies_wfr; auto. 
      destruct Hdp; auto.
    apply ABasic.ran_rf_is_read with E (p2X E p L) w'; auto.
      generalize (path_rf_wf E p L); intros [? [? ?]]; auto; 
        apply wfl_implies_wfr; auto.
        destruct Hdp; auto.
assert (exists w2, L (f (DR (w2,e2)))) as Hw2.
  exists w'; destruct Hdp as [[? ?] ?]; auto.
destruct Hw1 as [w1 Hl1]; destruct Hw2 as [w2 Hl2]. 
generalize H12; intros [w [Hdp1 Hrf2]].
assert (events E e1) as He1.
  apply ABasic.po_iico_domain_in_events with w; auto.
    apply tc_ppo_fences_in_po; auto.
assert (events E e2) as He2.
  apply ABasic.ran_rf_in_events with (p2X E p L) w; auto. 
    apply (path_rf_wf E p L); auto; apply wfl_implies_wfr; auto.
    destruct Hrf2 as [? ?]; auto.
generalize (hb_implies_p E p L w1 w2 e1 e2 phi Hwf Hudrp Htp Hacp Htotp Hphb Hmns Hwfl Hwfrfl Hwfd Hl1 Hl2 H12); intro Hp12.
assert (evt_of_devt (DR (w1,e1)) = e1) as Hde1.
  simpl; auto.
assert (evt_of_devt (DR (w2,e2)) = e2) as Hde2.
  simpl; auto.
generalize (tc_hb_implies_in_tc_p E p L w2 w1 e2 e1 phi Hwf Hudrp Htp Hacp Htotp Hphb Hmns Hwfl Hwfrfl Hwfd Hl2 Hl1 Hde2 Hde1 H21); intro Hp21.
assert (tc p (d (DR (w1,e1))) (d (DR (w1,e1)))) as Htcp1.
  apply trc_ind with (d (DR (w2,e2))); auto; apply trc_step; auto.
generalize Htcp1; fold (~(tc p (d (DR (w1,e1))) (d (DR (w1,e1))))); 
  apply (Hacp (d (DR (w1,e1)))).
Qed.

Lemma path_co_prop :
  forall E p L phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
(*  (forall w w' : Event, loc w = loc w' ->
    tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  machine_not_stuck E p L phi -> wf_labels E L -> wf_rf_labels E L -> 
  (forall e1 e2, 
     rel_seq (co (p2X E p L)) (A.prop E (p2X E p L)) e1 e2 -> 
     ~ (tc (rel_seq (co (p2X E p L)) (A.prop E (p2X E p L)))) e2 e1).
Proof.
intros E p L phi Hwf Hudrp Htp Hacp Htotp (*Hfifo*) Hmns Hwfl Hwfrfl e1 e2 H12 H21.
assert (linear_strict_order p L) as Hlp.
  split; [|split; [|split]]; auto.
    intros x1 x2 x3 [Hx12 Hx23]; apply Htp with x2; auto.
    intros x Hx; apply Hacp with x; apply trc_step; auto.
generalize H12; intros [w' [Hco Hprop]].
assert (L (f (DW e1))) as Hl1.
  destruct Hco as [? [? [? [l1 [l2 [Heq1 [Heq2 ?]]]]]]]; apply Hudrp; rewrite <- Heq1; left; exists l2; auto.
assert (L (f (DW e2))) as Hl2.
  apply dom_tc_co_in_L with E p e1; auto.
generalize (co_prop_implies_p E p L e1 e2 phi Hwf Hudrp Htp Hacp Htotp Hmns Hwfl Hwfrfl Hl1 Hl2 H12); intro Hp12.
generalize (tc_co_prop_implies_tc_p E p L e2 e1 phi Hwf Hudrp Htp Hacp Htotp (*Hfifo*) Hmns Hwfl Hwfrfl Hl2 Hl1 (*Hde2 Hde1*) H21); intro Hp21.
assert (tc p (f (DW e1)) (f (DW e1))) as Htcp1.
  apply trc_ind with (f (DW e2)); auto; apply trc_step; auto.
generalize Htcp1; fold (~(tc p (f (DW e1)) (f (DW e1)))); 
  apply (Hacp (f (DW e1))).
Qed.

Lemma wfl_e2 :
  forall E L e, 
  wf_labels E L -> wf_rf_labels E L ->
  events E e -> 
  (exists de, e = evt_of_devt de /\ L (f de)).
Proof.
intros E L e Hwfl Hwfrf He.

destruct Hwfl as [? [? [Hw ?]]].
destruct Hwfrf as [Hr ?].
assert (writes E e \/ reads E e) as Hor.
  case_eq (action e); intros d l v Hae; case_eq d; intro Hd.
    right; split; auto; exists l; exists v; subst; auto.
    left; split; auto; exists l; exists v; subst; auto.
destruct Hor as [Hwe | Hre].

  exists (DW e); split; auto; apply Hw; auto.
  generalize (Hr e Hre); intros [w [Hrfm Hl]];
    exists (DR (w,e)); split; auto; apply Hr; auto.
Qed.

Definition loc_of_label lb :=
  match lb with
  | d de | f de => loc (evt_of_devt de) end.

Lemma wbef_after :
  forall E B w r,
  well_formed_event_structure E ->
  w <> wbef E B r ->
  po_iico E w r -> loc w = loc r ->
  po_iico E w (wbef E B r).
Proof.
intros E B w r Hwf Hdiff Hwr Heql.
generalize (EPick.pick_in (fun w : Event =>
   B w /\
   loc r = loc w /\
   po_iico E w r /\ ~ (exists w' : Event, loc r = loc w' /\ po_iico E w w' /\ po_iico E w' r)));
fold (wbef E B r); intros [Hr [Hl [Hpo Hn]]].

assert (events E w) as Hew.
  apply ABasic.po_iico_domain_in_events with r; auto.
assert (events E (wbef E B r)) as Hewbef.
  apply ABasic.po_iico_domain_in_events with r; auto.  
assert (proc_of w = proc_of (wbef E B r)) as Heqp.
  rewrite ABasic.po_implies_same_proc with E w r; auto.
  rewrite ABasic.po_implies_same_proc with E (wbef E B r) r; auto.  
  apply ABasic.po_iico_range_in_events with w; auto.
  apply ABasic.po_iico_range_in_events with w; auto.

generalize (ABasic.same_proc_implies_po Hwf Heqp Hdiff Hew Hewbef);
intro Hor; inversion Hor as [|Hwbefw]; auto; clear Hor.

assert (exists w' : Event, loc r = loc w' /\ po_iico E (wbef E B r) w' /\ po_iico E w' r) as Hc.
  exists w; split; [|split]; auto.
contradiction.
Qed.

(*Lemma po_ws :
 forall (E : Event_struct) (p : Rln Label) (L : Ensemble Label)
   (w1 w2 : Event) phi,
 well_formed_event_structure E ->
 Included Label (Union Label (dom p) (ran p)) L ->
 trans p ->
 acyclic p ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
 machine_not_stuck E p L phi ->
 (forall l : Label, L l -> events E (evt_of_label l)) ->
 (forall e1 e2 : Event, L (d (DW e1)) -> L (d (DW e2)) -> po_iico E e1 e2 -> loc e1 = loc e2 -> p (d (DW e1)) (d (DW e2))) ->
(*  (forall w w', loc w = loc w' -> tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  wf_labels E L -> wf_rf_labels E L ->
  writes E w1 -> writes E w2 ->
  po_loc_llh E w1 w2 -> 
  ws (p2X E p L) w1 w2.-
Proof.
intros E p L w1 w2 phi Hwf Hudr Htp Hacp Htotp Hmns Hle Hpop (*Hfifo*) Hwfl Hwfrfl Hw1 Hw2 Hpio.

assert (write_serialization_well_formed (events E) (ws (p2X E p L))) as Hwswf.
  apply path_ws_wf; auto.
    destruct Hwfl as [? [? [? ?]]]; auto.
    split; [|split; [|split]]; auto.
      intros x1 x2 x3 [H12 H23]; apply Htp with x2; auto.
      intros x Hx; apply Hacp with x; apply trc_step; auto.

destruct (eqEv_dec w1 w2) as [Heq | Hneq].

  assert False as Ht.
    rewrite Heq in Hpio; destruct Hpio as [? [Hpo ?]].
    apply (ABasic.po_ac Hwf Hpo).
  inversion Ht.

assert (ws (p2X E p L) w1 w2 \/ ws (p2X E p L) w2 w1) as Hor.
  destruct Hwswf as [Hws_tot ?].
  generalize (Hws_tot (loc w1)); intro Hlin; destruct_lin Hlin.
  assert ((writes_to_same_loc_l (events E) (loc w1)) w1) as Hww1.
    destruct Hw1 as [? [l [v Haw]]]; 
    split; auto; exists v; unfold loc; rewrite Haw; auto.
  assert ((writes_to_same_loc_l (events E) (loc w1)) w2) as Hww2.
    destruct Hpio as [Hl ?]; rewrite Hl.
    destruct Hw2 as [? [l [v Haw]]]; 
    split; auto; exists v; unfold loc; rewrite Haw; auto.    
   
  generalize (Htot w1 w2 Hneq Hww1 Hww2); intros [[? ?]|[? ?]]; auto.

inversion Hor as [H12 | H21]; auto.

  assert (linear_strict_order p L) as Hlp.
    split; [|split; [|split]]; auto.
      intros x y z [Hxy Hyz]; apply Htp with y; auto.
      intros x Hx; apply Hacp with x; apply trc_step; auto.
  generalize (path_uniws E p L w1 w2 phi Hwf Hwfl Hwfrfl Hlp Hpop Hmns Hpio);
  intro; contradiction.
Qed.*)

Lemma pred_incl3 :
  forall (r:Rln Label) l1 l2,
  trans r ->
  r l1 l2 ->
  rel_incl (pred r l1) (pred r l2).
Proof.
intros r l1 l2 Htr H12 x y [? Hor]; split; auto.
  apply Htr with l1; auto.
Qed.

Lemma path_unifrrf : 
  forall E p L e1 e2 phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p -> wf_labels E L -> wf_rf_labels E L ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  machine_not_stuck E p L phi ->  
  po_loc_llh E e1 e2 -> ~ (rel_seq (fr E (p2X E p L)) (rf (p2X E p L))) e2 e1.
Proof.
intros E p L e1 e2 phi Hwf Hudr Htp Hacp Hwfl Hwfrfl Htotp Hmns [? [? Hnrr]] [w [Hfr Hrf]].
assert (rfmaps_well_formed E (events E) (rf (p2X E p L))) as Hrfwf.
    apply path_rf_wf; auto.
      split; [|split; [|split]]; auto.
        intros x1 x2 x3 [H12 H23]; apply Htp with x2; auto.
        intros x Hx; apply Hacp with x; apply trc_step; auto.

apply Hnrr; split; split.
  apply ABasic.ran_rf_in_events with (p2X E p L) w; auto.
  apply ABasic.ran_rf_is_read with E (p2X E p L) w; auto.
    destruct Hrfwf as [? [? ?]]; auto.

  apply ABasic.dom_fr_in_events with (p2X E p L) w; auto.
  apply ABasic.dom_fr_is_read with E (p2X E p L) w; auto.
Qed.

Lemma wbef_in_b :
  forall E (b:set Event) e,
  b (wbef E b e).
Proof.
intros E b e.
generalize (EPick.pick_in (fun w => b w /\ loc e = loc w /\
              po_iico E w e /\ ~(exists w', loc e = loc w' /\ po_iico E w w' /\ po_iico E w' e)));
fold (wbef E b e); intros [? ?]; auto.
Qed. (*might be a good idea to move it to intermediate_machine
            and track places where it's inlined*)

(*Lemma ran_int :
  forall E p n L s0 s1 e1 e2 e phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p -> 
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  (exists dr : Rln Label,
        trans dr /\
        rel_incl dr (pred p (f (DR (e, e2)))) /\
        (~
         (exists l' : Label,
            tc p (Last.last dr) l' /\ tc p l' (f (DR (e, e2)))) \/
         Last.last dr = f (DR (e, e2))) /\
        machine E dr L (f (DR (e, e2))) n phi (Some s0) (Some s1)) ->
  (forall w1 w2 : Event, L (d (DW w1)) -> L (d (DW w2)) ->
        po_iico E w1 w2 -> loc w1 = loc w2 -> p (d (DW w1)) (d (DW w2))) ->
  wf_rs E (B s1) ->
  (*B s1 (wbef E (B s1) e2) e ->*)
  writes E e1 ->
  po_loc E e1 e2 ->
  (B s1) e1.
Proof.
intros E p n L s0 s1 e1 e2 e Hwf Hwfl Hwfrfl Hudrp Htp Hacp Htotp Hm Hpoww Hwfb Hw1 (*Hbefe*) H12.
destruct (eqEv_dec e1 (wbef E (B s1) e2)) as [Heq | Hneq].
  generalize (udr_dB (B s1) e1); intros [dir bak].
  assert (udr (B s1) e1) as Hudr.
    left; exists e; rewrite Heq; auto.
  generalize (dir Hudr); intros [? ?]; exists dB; auto.
  destruct H12 as [Hloc Hpo].
  generalize (wbef_after E (B s1) e1 e2 Hwf Hneq Hpo Hloc); intro Hpowbefe1.
    generalize (EPick.pick_in (fun w => ran (B s1) w /\ loc e2 = loc w /\ po_iico E w e2 /\
        ~ (exists w' : Event, loc e2 = loc w' /\ po_iico E w w' /\ po_iico E w' e2)));
      fold (wbef E (B s1) e2); intros [Hr [Hil [Hipo Hn]]]; auto.

  assert (loc e1 = loc (wbef E (B s1) e2)) as Hl.
    rewrite Hloc; auto.
  assert (forall l : Label, L l -> events E (evt_of_label l)) as Hwfle.
    apply wfl_e; auto.
  assert (p (d (DW e1)) (d (DW (wbef E (B s1) e2)))) as Hww.
    apply Hpoww; auto; 
    generalize Hwfl; intro Hwfl'; destruct Hwfl' as [? [? [Hlfw Hdf]]]; 
    apply Hdf; apply Hlfw; auto.
    destruct Hwfb as [Hwfbw ?].
      apply Hwfbw; auto.
      right; auto.
      apply dB_not_in_E with E.
        apply ABasic.po_iico_domain_in_events with e2; auto.
  assert (p (d (DW (wbef E (B s1) e2))) (f (DR (e, e2)))) as Hwr.
    apply in_buff_implies_before with E L n s0 s1; auto.
    apply ABasic.po_iico_range_in_events with e1; auto.
    right; auto. 
  assert (~ (exists l' : Label, tc p (f (DR (e, e2))) l' /\ tc p l' (f (DR (e, e2)))) \/
          f (DR (e, e2)) = f (DR (e, e2))) as Hni.
    right; auto.
  assert (B s1 e1 (wbef E (B s1) e2)) as Hb.
    generalize (in_order_implies_in_obuff E p L (f (DR (e,e2))) n s0 s1 e1 (wbef E (B s1) e2) (f (DR (e,e2))) Hwf Hwfb Hudrp Htp Hacp Htotp
      Hl Hwfle Hww Hwr Hwr Hwfl Hni Hm); auto. 
  
  assert (udr (B s1) e1) as Hudr.
    left; exists (wbef E (B s1) e2); auto.
  generalize (udr_dB (B s1) e1); intros [dir bak].
  generalize (dir Hudr); intros [? ?]; exists dB; auto.
Qed.*) 

Lemma p_dw_dw :
  forall E p L w1 w2 phi,
  well_formed_event_structure E ->
  machine_not_stuck E p L phi ->
  wf_labels E L ->
  Included _ (Union _ (dom p) (ran p)) L -> 
  trans p -> acyclic p -> 
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  L (d (DW w1)) -> L (d (DW w2)) ->
  po_loc_llh E w1 w2 ->
  p (d (DW w1)) (d (DW w2)).
Proof.
intros E p L w1 w2 phi Hwf Hmns Hwfl Hudr Htp Hacp Htot Hl1 Hl2 H12.
assert (d (DW w1) <> d (DW w2)) as Hd.
  destruct H12 as [? [Hpo ?]];
  intro Heql; inversion Heql as [Heqs];
  rewrite Heqs in Hpo.
  generalize Hpo; apply ABasic.po_ac; auto.
generalize (Htot (d (DW w1)) (d (DW w2)) Hd Hl1 Hl2); intros [|H21]; auto.
generalize (Hmns (d (DW w1)) Hl1);
intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfcs [Hwfrcp [Hm Hs]]]]]]]]].
unfold step in Hs; unfold buff_write_step in Hs.
destruct (is_emp
           (Intersection Event (Rs s1) (fun r' : Event => A.fences E w1 r'))); [|inversion Hs].
case_eq (is_emp
           (Intersection _ (B s1)
              (fun e : Event => po_iico E w1 e /\ loc w1 = loc e))); intro Hb; 
rewrite Hb in Hs; [|inversion Hs].
generalize (is_emp_axt (B s1) (fun e : Event => po_iico E w1 e /\ loc w1 = loc e) Hb); intro Hn.
destruct H12 as [? [? ?]];
assert (exists e : Event, (B s1) e /\ po_iico E w1 e /\ loc w1 = loc e) as Hy.
  exists w2; split; [|split]; auto.
    apply in_order_implies_in_buff with E p L (d (DW w1)) n s0 (d (DW w1)) phi; auto.
      apply wfl_e; auto.
      apply if_ldw_then_lfw with E; auto.
      exists (pred p (d (DW w1))); split; [|split; [|split]]; auto.
        apply td_tpred; auto.
        intros x y Hxy; auto.
        left; apply Last.no_interv_last; auto; intros x y Hxy; auto.
contradiction.    
Qed.

Lemma po_loc_flush_contrad :
  forall E p L w1 w2 phi,
  well_formed_event_structure E ->
  machine_not_stuck E p L phi ->
  Included _ (Union _ (dom p) (ran p)) L -> 
  trans p -> acyclic p -> 
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  wf_labels E L -> wf_rf_labels E L ->
  po_loc_llh E w1 w2 ->
  p (f (DW w2)) (f (DW w1)) ->
  False.
Proof.
intros E p L w1 w2 phi Hwf Hmns Hudr Htp Hacp Htotp Hwfl Hwfrfl H12 H21.
  assert (linear_strict_order p L) as Hlp.
    split; [|split; [|split]]; auto.
      intros x1 x2 x3 [Hp12 Hp23]; apply Htp with x2; auto.
      intros x Hx; apply Hacp with x; apply trc_step; auto.
assert (L (f (DW w1))) as Hlf1.
  apply Hudr; right; exists (f (DW w2)); auto.
generalize (Hmns (f (DW w1)) Hlf1);
intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfcs [Hwfrcp [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_write_step in Hs.
assert (p (d (DW w2)) (f (DW w1))) as Hpd2f1.
  apply Htp with (f (DW w2)); auto.
    apply p_dw_fw with E L phi; auto.
      apply Hudr; left; exists (f (DW w1)); auto.
destruct (bin ((B s1)) w1); [|inversion Hs];
case_eq (bemp
            (rrestrict
               (fun w2 w3 : Event =>
                (po_loc E w2 w3 \/ A.prop E (p2X E p L) w2 w3) /\ w2 = w1)
               (fun e : Event => udr (Rcp s1) e))); intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (bemp_axt (fun w2 w3 : Event =>
           (po_loc E w2 w3 \/ A.prop E (p2X E p L) w2 w3) /\ w2 = w1) (fun e : Event => udr (Rcp s1) e) Hb); intro Hn;
apply Hn; exists w2; split; auto.
  exists w1; split; auto.
    left; destruct H12 as [? [? ?]]; split; auto.

    apply in_order_implies_in_rcp with E p L (f (DW w1)) n s0 (f (DW w1)) phi; auto.
      apply dB_not_in_E with E; auto.
        apply ABasic.po_iico_range_in_events with w1; auto; destruct H12 as [? [? ?]]; auto.
      exists (pred p (f (DW w1))); split; [|split; [|split]]; auto.
        apply td_tpred; auto.
        intros x y Hxy; auto.
        apply Last.no_interv_last; auto; intros x y Hxy; auto.      
Qed.

Hypothesis phi_rcp :
  forall E p L s0 (phi:FRcp) w1 w2,
  phi w1 w2 ->
  (exists m, exists lst, exists s, wf_buff E (Rcp s) /\ wf_rs E (Rs s) /\
      (exists r, trans r /\ rel_incl r ((pred p lst)) /\ 
      (~(exists l' : Label, tc p (Last.last r) l' /\
          tc p l' lst) \/ Last.last r = lst) /\
      machine E r L lst m phi (Some s0) (Some s)) /\
      Rcp s w1 w2).

Lemma poloc_fw_fw :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  (forall w1 w2 : Event, L (f (DW w1)) -> L (f (DW w2)) ->
    po_loc E w1 w2 -> p (f (DW w1)) (f (DW w2))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hlp Hmns w1 w2 Hl1 Hl2 H12.
assert (f (DW w1) <> f (DW w2)) as Hdiff.
  intro Heq; inversion Heq as [Heqw]; rewrite Heqw in H12.
  destruct H12 as [? Hpo]; apply (ABasic.po_ac Hwf Hpo).
assert (p (f (DW w2)) (f (DW w1)) \/ p (f (DW w1)) (f (DW w2))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [H21|]; clear Hor; auto.
generalize (Hmns (f (DW w1)) Hl1); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_write_step in Hs.
destruct (bin (B s1) w1); [|inversion Hs];
case_eq (bemp (rrestrict
               (fun w2 w3 : Event =>
                (po_loc E w2 w3 \/ A.prop E (p2X E p L) w2 w3) /\ w2 = w1)
               (fun e : Event => udr (Rcp s1) e))); intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (bemp_axt (fun w2 w3 : Event =>
           (po_loc E w2 w3 \/ A.prop E (p2X E p L) w2 w3) /\ w2 = w1) (fun e : Event => udr (Rcp s1) e) Hb);
intros Hn.
assert (exists e : Event, ran
          (fun w2 w3 : Event =>
           (po_loc E w2 w3 \/ A.prop E (p2X E p L) w2 w3) /\ w2 = w1) e /\
        udr (Rcp s1) e) as Hy.
  exists w2; split; auto.
    exists w1; split; auto.
  assert (trans p) as Htp.
    destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
  destruct_lin Hlp; apply in_order_implies_in_rcp with E p L (f (DW w1)) n s0 (f (DW w1)) phi; auto.
    intros x Hx; apply Hac with x; auto; rewrite <- trans_tc with Label p; auto.
    apply dB_not_in_E with E; auto; apply ABasic.po_iico_range_in_events with w1; destruct H12; auto. 
    exists (pred p (f (DW w1))); split; [|split; [|split]]; auto.
      apply td_tpred; auto. intros x y Hxy; auto.
      apply Last.no_interv_last; auto.
      intros x y Hxy; auto.
contradiction.
Qed.

Lemma path_unifr : 
  forall E p L e1 e2 phi,
  well_formed_event_structure E ->
  wf_labels E L ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p -> wf_labels E L -> wf_rf_labels E L ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  (forall w1 w2, L (d (DW w1)) -> L (d (DW w2)) -> po_iico E w1 w2 -> 
     loc w1 = loc w2 -> p (d (DW w1)) (d (DW w2))) ->
(* (forall w w', loc w = loc w' -> tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
 (forall l : Label, L l -> events E (evt_of_label l)) ->
  machine_not_stuck E p L phi ->  
  po_loc_llh E e1 e2 -> ~ fr E (p2X E p L) e2 e1.
Proof.
intros E p L e1 e2 phi Hwf Hwfl Hudrp Htp Hacp Hwflb Hwfrfl Htotp Hpoww (*Hfifo*) Hle Hmns H12 [He2 [He1 [e [Hrf Hws]]]].
generalize Hrf; intros Hrfee2.

assert (L (f (DR (e,e2)))) as Hlfe2.
  destruct Hrfee2 as [? ?]; auto.
generalize (Hmns (f (DR (e,e2))) Hlfe2);
intros [n [s0 [s1 [s2 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]]; simpl in Hs; 
unfold flush_resolved_read_step in Hs.

  assert (linear_strict_order p L) as Hlp.
    split; [|split; [|split]]; auto.
      intros x1 x2 x3 [Hp12 Hp23]; apply Htp with x2; auto.
      intros x Hx; apply Hacp with x; apply trc_step; auto.

destruct (bin (Rs s1) e2); [|inversion Hs].
destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) e2 e))); [|inversion Hs].
destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) e2 e))); [|inversion Hs].
unfold visible in Hs.
destruct (is_emp (Intersection _ (B s1) (fun e => po_loc E e2 e))); [|inversion Hs].
  destruct (eqEv_dec (wbef E (B s1) e2) dB); [|inversion Hs].
    generalize (wbef_dB E (B s1) e2); intros [dir ?]; generalize (dir e0); intro Hn.
    apply Hn; exists e1; destruct H12 as [? [? ?]]; split; auto.

  case_eq (bin (fun e0 : Event =>
            (e0 = wbef E (B s1) e2 \/ phi (wbef E (B s1) e2) e0) /\
            loc e2 = loc e0 (*\/
            po_loc E e0 e2 /\
            ~(exists e' : Event,
               writes E e' /\
               loc e' = loc e2 /\ po_loc E e0 e' /\ po_loc E e' e2) /\ 
            e0 = e*)) e); intro Hbef; rewrite Hbef in Hs; [|inversion Hs].
  generalize (bin_In (fun e0 : Event =>
            (e0 = wbef E (B s1) e2 \/ phi (wbef E (B s1) e2) e0) /\
            loc e2 = loc e0) e Hbef);
  intros [Hb Heql].

  inversion Hb as [Hwbef | Hrwbefe]; clear Hb. 
 
   generalize (EPick.pick_in (fun w => (B s1) w /\ loc e2 = loc w /\ po_iico E w e2 /\
        ~ (exists w' : Event, loc e2 = loc w' /\ po_iico E w w' /\ po_iico E w' e2)));
      fold (wbef E (B s1) e2); intros [Hr [Hl [Hpo Hn]]]; auto.
      destruct H12 as [? [? ?]]; apply Hn; exists e1; split; [|split]; auto.
        rewrite <- Hwbef. 
     assert (proc_of e = proc_of e1) as Heqp.
       rewrite <- Hwbef in Hpo.
       rewrite ABasic.po_implies_same_proc with E e e2; auto.
       rewrite ABasic.po_implies_same_proc with E e1 e2; auto.
       apply ABasic.po_iico_domain_in_events with e2; auto.
     generalize Hws; intro; destruct Hws as [Hwe [Hwe1 [Heqloc [le [l1 [Hlwe [Hlw1 Hco]]]]]]].
     assert (e <> e1) as Hdiff.
       intro Heq; rewrite Heq in Hlwe; rewrite <- Hlwe in Hlw1; rewrite Hlw1 in Hco.
       apply Hacp with le; apply trc_step; auto.
     assert (Ensembles.In Event (events E) e) as Hee.
       destruct Hwe; auto.
     assert (Ensembles.In Event (events E) e1) as Hee1.
       destruct Hwe1; auto.
     generalize (ABasic.same_proc_implies_po Hwf Heqp Hdiff Hee Hee1);
     intros [|He1e]; auto.
      assert (po_loc_llh E e1 e) as Hllh.
        split; [|split]; auto.
        intros [[? [? [? Hr1]]] ?]; destruct Hwe1 as [? [? [? Hw1]]];
        rewrite Hr1 in Hw1; inversion Hw1.

      generalize (path_uniws E p L e1 e phi Hwf Hwfl Hwfrfl Hlp Hpoww (*Hfifo*) Hmns Hllh); intro Hnco;
      contradiction.

  assert (L (f (DW e1))) as Hl1.
    destruct Hws as [? [? [? [le [le1 [Hlfe [Hlfe1 Hp]]]]]]].
    apply Hudrp; right; exists le; rewrite <- Hlfe1; auto.
  
  assert (L (f (DW e))) as Hlfe.
    destruct Hws as [? [? [? [le [le1 [Hlfe [Hlfe1 Hp]]]]]]].
    apply Hudrp; left; exists le1; rewrite <- Hlfe; auto.

  generalize (phi_rcp E p L s0 phi (wbef E (B s1) e2) e Hrwbefe).
  intros [m [lst [s [Hwfrcp' [Hwfrs' [Hex Hrcp]]]]]].

  generalize (EPick.pick_in (fun w => (B s1) w /\ loc e2 = loc w /\ po_iico E w e2 /\
     ~ (exists w' : Event, loc e2 = loc w' /\ po_iico E w w' /\ po_iico E w' e2)));
  fold (wbef E (B s1) e2); intros [? [Hl [Hwb2 Hniw]]].

  assert (loc (wbef E (B s1) e2) = loc e) as Heql'.
    rewrite <- Hl; auto.

  destruct (eqEv_dec (wbef E (B s1) e2) e1) as [Heq | Hneq].
    rewrite Heq in Hrwbefe.
    assert (p (f (DW e1)) (f (DW e1))) as Hc.
      apply Htp with (f (DW e)).
        rewrite <- Heq; apply rcp_p with E L m s0 s lst phi; auto.
        destruct Hws as [? [? [? [le [le1 [Hllfe [Hlfe1 Hp]]]]]]].
          rewrite <- Hllfe; rewrite <- Hlfe1; auto.
    apply Hacp with (f (DW e1)); apply trc_step; auto.

    assert (e1 <> wbef E (B s1) e2) as Hdiff.
      auto.
    assert (Ensembles.In Event (events E) (wbef E (B s1) e2)) as Hewb.
      apply ABasic.po_iico_domain_in_events with e2; auto.

    assert (proc_of e1 = proc_of (wbef E (B s1) e2)) as Hproc.
      rewrite ABasic.po_implies_same_proc with E (wbef E (B s1) e2) e2; auto.
      destruct H12 as [? [? ?]]; apply ABasic.po_implies_same_proc with E; auto.

    assert (po_iico E e1 (wbef E (B s1) e2)) as Hpo.
      generalize (ABasic.same_proc_implies_po Hwf Hproc Hdiff He1 Hewb); intros [|Hwb1]; auto.
      assert False as Ht.
        destruct H12 as [? [? ?]]; apply Hniw; exists e1; split; [|split]; auto.
      inversion Ht.

    assert (p (f (DW e1)) (f (DW e1))) as Hc.
      apply Htp with (f (DW (wbef E (B s1) e2))).
        apply poloc_fw_fw with E L phi; auto.
          destruct Hwfl as [? [? [Hwl ?]]]; apply Hwl; auto.
          split; auto; rewrite <- Hl; auto; destruct H12 as [? [? ?]]; auto.
        apply Htp with (f (DW e)).
        apply rcp_p with E L m s0 s lst phi; auto. 
          destruct Hws as [? [? [? [le [le1 [Hllfe [Hlfe1 Hp]]]]]]].
            rewrite <- Hllfe; rewrite <- Hlfe1; auto.          
   apply Hacp with (f (DW e1)); apply trc_step; auto.
Qed.      

Lemma path_uniproc :
  forall E p L phi,
  well_formed_event_structure E ->
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2, l1 <> l2 -> (L l1) -> L l2 -> p l1 l2 \/ p l2 l1) ->
  (forall w1 r1 w2, L (f (DR (w1,r1))) -> L (d (DW w2)) -> po_iico E r1 w2 -> 
     loc r1 = loc w2 -> p (f (DR (w1,r1))) (d (DW w2))) ->
  (forall w1 w2 : Event, L (d (DW w1)) -> L (d (DW w2)) ->
  po_iico E w1 w2 -> loc w1 = loc w2 -> p (d (DW w1)) (d (DW w2))) ->
(*  (forall w w' : Event, loc w = loc w' ->
    tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  machine_not_stuck E p L phi -> wf_labels E L -> wf_rf_labels E L ->
  (forall e1 e2, po_loc_llh E e1 e2 -> ~ AWmm.com' E (p2X E p L) e2 e1).
Proof.
intros E p L phi Hwf Hudrp Htp Hacp Htotp Hporw Hpoww (*Hfifo*) Hmns Hwfl Hwfrfl e1 e2 H12 H21; 
  inversion H21 as [[[[Hrf | Hfr]|Hws]|Hwsrf] | Hfrrf]; clear H21.

  generalize Hrf; fold (~(rf (p2X E p L) e2 e1)); apply path_unirf with phi; auto.
    split; [|split; [|split]]; auto.
    intros x1 x2 x3 [H1 H2]; apply Htp with x2; auto.
    intros x Hx; apply Hacp with x; apply trc_step; auto.

  generalize Hfr; fold (~(fr E (p2X E p L) e2 e1)); apply path_unifr with phi; auto.
    apply wfl_e; auto.

  generalize Hws; fold (~(ws (p2X E p L) e2 e1)); apply path_uniws with phi; auto.
    split; [|split; [|split]]; auto.
      intros x y z [Hxy Hyz]; apply Htp with y; auto.
      intros x Hx; apply Hacp with x; apply trc_step; auto.

  generalize Hwsrf; fold (~(rel_seq (ws (p2X E p L)) (rf (p2X E p L)) e2 e1)); apply path_uniwsrf with phi; auto.
    apply wfl_w; auto. 

  generalize Hfrrf; fold (~(rel_seq (fr E (p2X E p L)) (rf (p2X E p L)) e2 e1)); apply path_unifrrf with phi; auto.
Qed.

Hypothesis prop_ran_W :
  forall E X e1 e2, A.prop E X e1 e2 -> writes E e2.

Lemma prop_hb_d_d :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  wf_devts E -> 
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->  
  (forall w1 de2, L (d (DW w1)) -> L (d de2) ->
   rel_seq (A.prop E (p2X E p L)) ((*rc*) (AWmm.hb E (p2X E p L))) w1 (evt_of_devt de2) -> 
   p (d (DW w1)) (d de2)).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hwfd Hlp Hmns w1 de2 Hl1 Hl2 [e [H1e He2]].
assert (L (d (DW e))) as Hle.
  destruct Hwfl as [? [? [Hlf Hdf]]]; apply Hdf; apply Hlf; auto.
  apply prop_ran_W with (p2X E p L) w1; auto.
generalize Hlp; intro Hlin; destruct_lin Hlp; apply Htrans with (d (DW e)); split; auto.
  apply prop_d_d with E L phi; auto.
  apply hb_d_d with E L phi; auto.
Qed. 

Hypothesis co_phi :
  forall X phi w1 w2,
  co X w1 w2 -> phi w1 w2.

Lemma irrefl_fr_long_cumul :
  forall E p L x y phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  wf_devts E -> 
  linear_strict_order p L ->
  (forall de1 de2, L (d de1) -> L (d de2) -> rfe (p2X E p L) (evt_of_devt de1) (evt_of_devt de2) -> p (d de1) (d de2)) ->
  (forall w1 de2, L (d (DW w1)) -> L (d de2) -> rel_seq (A.prop E (p2X E p L)) ((AWmm.hb E (p2X E p L))) w1 (evt_of_devt de2) -> p (d (DW w1)) (d de2)) -> 
  (*^ here we might have to weaken this hyp by saying that de2 is a read*)
(*  (forall w w' : Event, loc w = loc w' ->
    tc p (f (DW w)) (f (DW w')) -> tc p (d (DW w)) (d (DW w'))) ->*)
  machine_not_stuck E p L phi ->
  fr E (p2X E p L) x y -> 
  (rel_seq (A.prop E (p2X E p L)) ((AWmm.hb E (p2X E p L)))) y x ->
  False.
Proof.
intros E p L x e phi Hwf Hwfl Hwfrfl Hwfd Hlp Hrf Hphb (*Hfifo*) Hmns Hfr Hlc.
  assert (events E x) as Hex.
    apply ABasic.dom_fr_in_events with (p2X E p L) e; auto.
  assert (reads E x) as Hrx.
    split; auto.
      apply ABasic.dom_fr_is_read with E (p2X E p L) e; auto; apply path_rf_wf; auto.
  generalize (wfl_e2 E L x Hwfl Hwfrfl Hex); intros [dx [Hdx Hlfx]]; auto.
assert (evt_of_devt dx = x) as Hdx'.
  auto.
assert (exists wx, L (d (DR (wx,x)))) as Hexx.
  destruct Hwfl as [? [? [? Hfd]]].
  destruct Hwfrfl as [Hlfr ?]; generalize (Hlfr x Hrx); intros [wx [? Hfx]]; 
  exists wx; apply Hfd; auto.
destruct Hexx as [wx Hldx];
generalize (Hmns (d (DR (wx,x))) Hldx);
intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]];
simpl in Hs; unfold buff_read_step in Hs. 
case_eq (okw E (B s1) wx x); intro Hok; rewrite Hok in Hs; [|inversion Hs];
destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) x e))); [|inversion Hs].
case_eq (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = wx) 
              (fun e => rel_seq (A.prop E (p2X E p L)) ((AWmm.hb E (p2X E p L))) e x))); intro Hilc; [clear Hs |rewrite Hilc in Hs; inversion Hs].
generalize (bemp_axt (fun w1 w2 => phi w1 w2 /\ w1 = wx) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (AWmm.hb E (p2X E p L))) e x) Hilc); clear Hilc; intro Hn.

  assert (Included Label (Union Label (dom p) (ran p)) L) as Hudr.
    destruct_lin Hlp; auto.
  assert (trans p) as Htp.
    destruct_lin Hlp; auto.
    intros e1 e2 e3 H12 H23; apply Htrans with e2; auto.    
  assert (acyclic p) as Hacp.
    destruct_lin Hlp; auto.
    intros a Ha; apply Hac with a; auto; rewrite trans_tc in Ha; auto.
  assert (forall l1 l2 : Label, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) as Htotp.
    destruct_lin Hlp; auto.
  assert (forall l : Label, L l -> events E (evt_of_label l)) as Hle.
    apply wfl_e; auto.

  apply Hn; exists e; split; auto.
    destruct Hfr as [? [? [w [Hrfx Hco]]]].
    assert (w = wx) as Heqw.
      destruct Hrfx as [? ?].
      destruct Hwfrfl as [? [Hdl ?]]; apply Hdl with x; auto.
      destruct Hwfl as [? [? [? Hfd]]]; apply Hfd; auto.
        
    exists w; split; auto.
      apply co_phi with (p2X E p L); auto.
(*        exists n; exists (d (DR (wx,x))); exists s1; split; [|split; [|split]]; auto.
        exists (pred p (d (DR (wx,x)))); split; [|split; [|split]]; auto.
          apply td_tpred; auto. intros e1 e2 H12; auto.
          left; apply Last.no_interv_last; auto; intros e1 e2 H12; auto.
 
      apply ws_rcp with E p L (d (DR (wx,x))) n s0 phi; auto.
      generalize (in_order_implies_in_rcp E p L (d (DR (wx,x))) n s0 s1 (d (DR (wx,x))) w phi Hudr Htp Hacp Htotp Hwfrfl Hldx); auto.*)
       
(*        rewrite trans_tc in Hwxp; auto. rewrite trans_tc in Hwxp; auto.
        destruct Hco as [? [? [? [lw [le [Heqlw [Heqle Hp]]]]]]].
        destruct_lin Hlp; apply Hdr; rewrite <- Heqlw; left; exists le; auto.*)

(*      assert (L (f (DW e))) as Hlfe.
        destruct Hco as [? [? [? [lw [le [Heqlw [Heqle Hp]]]]]]].
        destruct_lin Hlp; apply Hdr; rewrite <- Heqle; right; exists lw; auto.*)

(*      exists dB; apply in_order_implies_in_buff with E p L (d (DR (wx,x))) n s0 (d (DR (wx,x))); auto.
        apply Hphb; auto.
        destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.
        apply Hphb; auto.
        destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.*)

(*contradiction.*)
Qed.

Lemma poloc_fr_dw :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  (forall w1 r1 w2, L (f (DR (w1,r1))) -> L (d (DW w2)) -> 
     po_iico E r1 w2 -> loc r1 = loc w2 -> p (f (DR (w1,r1))) (d (DW w2))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hlp Hmns w1 r1 w2 Hl1 Hl2 H12 Hloc.
assert (d (DW w2) <> f (DR (w1,r1))) as Hdiff.
  intro Heq; inversion Heq.
assert (p (d (DW w2)) (f (DR (w1, r1))) \/ p (f (DR (w1, r1))) (d (DW w2))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [Hdf |]; clear Hor; auto.
generalize (Hmns (f (DR (w1,r1))) Hl1); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold flush_resolved_read_step in Hs.
destruct (bin (Rs s1) r1); [|inversion Hs].
destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e))); [|inversion Hs];
destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e))); [|inversion Hs].
unfold visible in Hs.
case_eq (is_emp (Intersection _ (B s1) (fun e : Event => po_loc E r1 e))); intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (is_emp_axt (B s1) (fun e => po_loc E r1 e) Hb); intro Hn.
assert (exists e : Event, (B s1) e /\ po_loc E r1 e) as Hy.
  exists w2; split; auto.
  assert (trans p) as Htp.
    destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
  destruct_lin Hlp; apply in_order_implies_in_buff with E p L (f (DR (w1,r1))) n s0 (f (DR (w1,r1))) phi; auto.
    intros x Hx; apply Hac with x; auto; rewrite <- trans_tc with Label p; auto.
    apply wfl_e; auto. 
    apply if_ldw_then_lfw with E; auto; apply Hdr; left; exists (f (DR (w1,r1))); auto.
    exists (pred p (f (DR (w1, r1)))); split; [|split; [|split]]; auto.
      apply td_tpred; auto. intros x y Hxy; auto.
      left; apply Last.no_interv_last; auto.
      intros x y Hxy; auto.
      split; auto.
contradiction.
Qed.

Lemma same_cs :
  forall E (p:Rln Label) L s0 s1 lb w phi,
  events E w ->
  step E p L (Some s0) lb phi = Some s1 ->
  wf_rf_labels E L ->
  (Cs s0) w ->
  (Cs s1) w.
Proof.
intros E p L s0 s1 lb w' phi Hew' Hs Hwfrf Hi0.
case_eq lb; intros de Hde; rewrite Hde in Hs; clear Hde; case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_read_step in Hs;
  destruct (okw E (B s0) w r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (bemp
             (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w)
                (fun e : Event =>
                 rel_seq (A.prop E (p2X E p L)) (AWmm.hb E (p2X E p L)) e r))); [|inversion Hs];
  inversion Hs as [Heq]; auto. 

  intros w Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold buff_write_step in Hs;
  destruct (is_emp
           (Intersection Event (Rs s0) (fun r' : Event => A.fences E w r'))); [|inversion Hs];
  destruct (is_emp
            (Intersection _ (B s0)
               (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s0) (fun e : Event => A.prop E (p2X E p L) w e))); [|inversion Hs];
  inversion Hs as [Heq]; auto.

  intros [w r] Hde; rewrite Hde in Hs; clear Hde; unfold step in Hs; 
  unfold flush_resolved_read_step in Hs;
  destruct (bin (Rs s0) r); [|inversion Hs];
  destruct (is_emp
            (Intersection Event (Rs s0)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
  destruct (is_emp
             (Intersection _ (B s0)
                (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (visible E (*p L*) s0 w r phi); [|inversion Hs].
  inversion Hs as [Heq]; auto.
    simpl; unfold upd_rs; left; auto. 

  intros w Hde; rewrite Hde in Hs; clear Hde;
  unfold step in Hs; unfold flush_write_step in Hs.
  destruct (bin ((B s0)) w); [|inversion Hs].
  destruct (bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
               w1 = w) (fun e : Event => udr (Rcp s0) e))); [|inversion Hs].
  inversion Hs as [Heq]; auto.
Qed. 

Lemma in_order_implies_in_cs :
  forall E (p:Rln Label) L lst n s0 s1 lb w r phi,
  Included _ (Union _ (dom p) (ran p)) L ->  
  trans p ->
  acyclic p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->  
  wf_rf_labels E L ->
  L lb -> 
  p (f (DR (w,r))) lb -> p (f (DR (w,r))) lst ->
  wf_rs E (Cs s1) ->
  (~ (exists l' : Label, tc p lst l' /\ tc p l' lb) \/ lst = lb) ->
  (exists d, trans d /\ rel_incl d (pred p lb) /\ 
     ~(exists l', tc p (Last.last d) l' /\ tc p l' lst) /\
     machine E d L lst n phi (Some s0) (Some s1)) ->
  (Cs s1) r.
Proof.
intros E p L lst n s0 s2 lb'' w r phi Hudrp Htp Hacp Htotp Hwfr Hllb Hprlb Hprlst Hwfrcp Hni Hm.
generalize s2 lst lb'' Hwfr Hm Hllb Hprlb Hprlst Hwfrcp Hni; 
clear s2 lst lb'' Hwfr Hm Hllb Hprlb Hprlst Hwfrcp Hni; 
induction n; 
intros s2 lst lb'' Hwfr [pd [Htd [Hi [Hniw Hm]]]] Hllb Hprlb Hprlst Hwfrcp Hni.
  
  destruct Hm as [? [Heof ?]]; auto.
    assert False as Ht.
      apply Hniw; rewrite Heof; exists (f (DR (w,r))); split; auto;
      apply trc_step; auto. apply EOF_bef; auto.
    inversion Ht.

  destruct Hm as [lb [s1 [Hdlb [Hm [Hs [? [Hwfq [? Hwfcs']]]]]]]];
  fold (machine E (pred pd lb) L lb n phi (Some s0) (Some s1)) in Hm.
  destruct (eqLabel_dec lb (f (DR (w,r)))) as [Heqlbr | Hneqlbr].
    rewrite Heqlbr in Hs; unfold step in Hs; unfold flush_resolved_read_step in Hs.
    destruct (bin (Rs s1) r); [|inversion Hs];
    destruct (is_emp
            (Intersection Event (Rs s1)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
    destruct (is_emp
             (Intersection _ (B s1)
                (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
    destruct (visible E (*pd L*) s1 w r phi) in Hs; inversion Hs; 
      simpl; auto; right; auto; unfold Ensembles.In; auto.

  assert (exists d, trans d /\ rel_incl d (pred p lb) /\
          ~ (exists l' : Label, tc p (Last.last d) l' /\ tc p l' lb) /\
          machine E d L lb n phi (Some s0) (Some s1)) as Hex.
    exists (pred pd lb); split; [|split; [|split]]; auto. 
      apply (td_tpred pd lb Htd).
      intros x y [Hxy Hylb]; 
      generalize (Hi x y Hxy); intros [? ?];
      generalize (Hi y lb Hylb); intros [? ?]; split; auto.
      apply Last.no_interv_last; auto. 
        intros x y Hxy; generalize (Hi x y Hxy); intros [? ?]; auto.
  assert (L lb) as Hlb.
    apply Hudrp; auto.
    generalize (Last.last_in_ran pd lb Hdlb); intros [x Hx];
    generalize (Hi x lb Hx); intros [? ?]; right; exists x; auto.
  assert (~ (exists l' : Label, tc p lb l' /\ tc p l' lb) \/ lb = lb) as Hnieq.
    auto.
  assert (p (f (DR (w,r))) lb) as Hrlb.
    assert (L (f (DR (w,r)))) as Hlr.
      apply Hudrp; left; exists lb''; auto.
    generalize (Htotp lb (f (DR (w,r))) Hneqlbr Hlb Hlr); intros [Hlbr | ?]; auto.
    assert (exists l' : Label, tc p (Last.last pd) l' /\ tc p l' lst) as Hc.
      rewrite Hdlb; exists (f (DR (w,r))); split; apply trc_step; auto.
    contradiction.
  generalize (IHn s1 lb lb Hwfr Hex Hlb Hrlb Hrlb Hwfcs' Hnieq); intro Hi1.

  apply (same_cs E pd L s1 s2 lb r phi); auto.
    generalize (Hwfcs' r Hi1); intros [? ?]; auto.
Qed.

Lemma poloc_dw_dw :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  (forall w1 w2 : Event, L (d (DW w1)) -> L (d (DW w2)) ->
    po_loc E w1 w2 -> p (d (DW w1)) (d (DW w2))).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hlp Hmns w1 w2 Hl1 Hl2 H12.
assert (d (DW w1) <> d (DW w2)) as Hdiff.
  intro Heq; inversion Heq as [Heqw]; rewrite Heqw in H12.
  destruct H12 as [? Hpo]; apply (ABasic.po_ac Hwf Hpo).
assert (p (d (DW w2)) (d (DW w1)) \/ p (d (DW w1)) (d (DW w2))) as Hor.
  destruct_lin Hlp; apply Htot; auto.
inversion Hor as [H21|]; clear Hor; auto.
generalize (Hmns (d (DW w1)) Hl1); intros [n [s0 [s1 [s2 [Hwfb [Hwfrs [Hwfrcp [Hwfcs [Hm Hs]]]]]]]]].
unfold step in Hs; unfold buff_write_step in Hs.
destruct (is_emp (Intersection Event (Rs s1) (fun r' : Event => (A.fences E) w1 r'))); [|inversion Hs];
case_eq (is_emp (Intersection _ (B s1) (fun e : Event => po_iico E w1 e /\ loc w1 = loc e))); intro Hb; rewrite Hb in Hs; [|inversion Hs].
generalize (is_emp_axt (B s1) (fun e : Event => po_iico E w1 e /\ loc w1 = loc e) Hb);
intros Hn.
assert (exists e : Event, (B s1) e /\ po_iico E w1 e /\ loc w1 = loc e) as Hy.
  exists w2; split; auto.
  assert (trans p) as Htp.
    destruct_lin Hlp; intros x y z Hxy Hyz; apply Htrans with y; auto.
  destruct_lin Hlp; apply in_order_implies_in_buff with E p L (d (DW w1)) n s0 (d (DW w1)) phi; auto.
    intros x Hx; apply Hac with x; auto; rewrite <- trans_tc with Label p; auto.
    apply wfl_e; auto. 
    apply if_ldw_then_lfw with E; auto; apply Hdr; left; exists (d (DW w1)); auto.    
    exists (pred p (d (DW w1))); split; [|split; [|split]]; auto.
      apply td_tpred; auto. intros x y Hxy; auto.
      left; apply Last.no_interv_last; auto.
      intros x y Hxy; auto.
      destruct H12; auto.
contradiction.
Qed.

Theorem from_mach_to_ax :
  forall E p L phi,
  well_formed_event_structure E ->
  wf_labels E L -> wf_rf_labels E L ->
  wf_devts E -> 
  linear_strict_order p L ->
  machine_not_stuck E p L phi ->
  AWmm.valid_execution E (p2X E p L).
Proof.
intros E p L phi Hwf Hwfl Hwfrfl Hwfd Hlp Hmns.
generalize (poloc_fr_dw E p L phi Hwf Hwfl Hwfrfl Hlp Hmns); intro Hporw.
generalize (poloc_dw_dw E p L phi Hwf Hwfl Hwfrfl Hlp Hmns); intro Hpoww.
generalize (hb_d_d E p L phi Hwf Hwfl Hwfrfl Hwfd Hlp Hmns); intro Hphb.
generalize (prop_hb_d_d E p L phi Hwf Hwfl Hwfrfl Hwfd Hlp Hmns); intro Hprophb.
(*generalize (p_fifo E p L Hwf Hwfl Hwfrfl Hwflp Hlp Hmns); intro Hfifo.*)
assert (forall w, writes E w -> L (f (DW w))) as Hlw.
  apply wfl_w; auto.
generalize (path_ws_wf E p L Hlw Hlp); intro Hwswf.
generalize (path_rf_wf E p L Hlp Hwfrfl); intro Hrfwf.
split; [|split; [|split; [|split; [|split]]]]; auto.

    destruct_lin Hlp.
    assert (trans p) as Htp.
      intros e1 e2 e3 H12 H23; apply Htrans with e2; auto.      
      unfold AWmm.uniproc; unfold AWmm.com_vs_po. apply path_uniproc with phi; auto.
        apply irr_trans_ac; auto; intros [x Hx]; apply (Hac x Hx).
      intros w1 w2 Hl1 Hl2 Hpo Hloc; apply Hpoww; auto; split; auto.

  intros x Hx.
    assert (~(exists x, rfe (p2X E p L) x x)) as Hrf_irr.
      intros [e [He ?]]; destruct Hrfwf as [? [Hrfm ?]];
      generalize (ABasic.ran_rf_is_read E (p2X E p L) e e Hrfm He); intros [? [? Hre]];
      generalize (ABasic.dom_rf_is_write E (p2X E p L) e e Hrfm He); intros [? [? Hwe]];
        rewrite Hre in Hwe; inversion Hwe; auto.   
    assert (~(exists x, tc (rel_union (A.ppo E) (A.fences E)) x x)) as Hdp_irr.
      intros [e He]; generalize (tc_ppo_fences_in_po E e e Hwf He); apply ABasic.po_ac; auto.
    assert (~(exists x, rel_union (rfe (p2X E p L)) (tc (rel_union (A.ppo E) (A.fences E))) x x)) as Hu_irr.
      intros [e He]; inversion He as [Hrf | Hdp].
        apply Hrf_irr; exists e; auto.
        apply Hdp_irr; exists e; auto.
    assert (trans (tc (rel_union (A.ppo E) (A.fences E)))) as Htdp.
      intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
    assert (trans (rfe (p2X E p L))) as Htrf.
      intros e1 e2 e3 [H12 ?] [H23 ?]; destruct Hrfwf as [? [Hrfm ?]];
      generalize (ABasic.ran_rf_is_read E (p2X E p L) e1 e2 Hrfm H12); intros [? [? Hr2]];
      generalize (ABasic.dom_rf_is_write E (p2X E p L) e2 e3 Hrfm H23); intros [? [? Hw2]];
        rewrite Hr2 in Hw2; inversion Hw2; auto.      
    generalize (union_cycle_implies_seq_cycle2 Hrf_irr Hdp_irr Hu_irr Htdp Htrf Hx); 
    intros [y Hy]; clear Hrf_irr Hdp_irr Hu_irr Htdp Htrf x Hx; 
    generalize (tc_dec Hy); intros [z [Hyz [Hzy | Heqzy]]].
      destruct_lin Hlp.
      assert (trans p) as Htp.
        intros e1 e2 e3 H12 H23; apply Htrans with e2; auto.
      generalize Hzy; apply path_hb with phi; auto.
        apply irr_trans_ac; auto; intros [x Hx]; apply (Hac x Hx).
      rewrite Heqzy in Hyz.
        destruct_lin Hlp; generalize Hyz; apply hb_irr; auto.

  unfold irrefl; intros x [y [Hfr Hlc]]; apply irrefl_fr_long_cumul with E p L x y phi; auto.
  intros de1 de2 Hlde1 Hlde2 Hrf; apply Hphb; auto.
    left; auto.

  intros x Hx.
    assert (~(exists x, co (p2X E p L) x x)) as Hco_irr.
      intros [e [? [? [? [l1 [l2 [Hl1 [Hl2 Hp]]]]]]]];
      rewrite Hl1 in Hp; rewrite Hl2 in Hp; destruct_lin Hlp; apply Hac with (f (DW e)); auto.
    assert (~(exists x, (A.prop E (p2X E p L)) x x)) as Hprop_irr.
      apply A.prop_valid; auto.
    assert (~(exists x, rel_union (A.prop E (p2X E p L)) (co (p2X E p L)) x x)) as Hu_irr.
      intros [e He]; inversion He as [Hco | Hprop].
        apply Hprop_irr; exists e; auto.
        apply Hco_irr; exists e; auto.
    assert (trans (A.prop E (p2X E p L))) as Htprop.
      apply A.prop_trans; auto.
    assert (trans (co (p2X E p L))) as Htco.
      intros e1 e2 e3 [? [? [Hloc [l1 [l2 [Hl1 [Hl2 Hp12]]]]]]] [? [? [Hloc' [l2' [l3 [Hl2' [Hl3 Hp23]]]]]]].
      split; [|split; [|split]]; auto. 
        rewrite Hloc; rewrite Hloc'; auto.
        exists l1; exists l3; split; [|split]; auto.
        destruct_lin Hlp; apply Htrans with l2; split; auto; rewrite Hl2; rewrite <- Hl2'; auto. 
    assert (tc (rel_union (A.prop E (p2X E p L)) (co (p2X E p L))) x x) as Hx'.
      rewrite rel_union_refl; auto.
    generalize (union_cycle_implies_seq_cycle2 Hprop_irr Hco_irr Hu_irr Htco Htprop Hx'); 
    intros [y Hy]; clear Hco_irr Hprop_irr Hu_irr Htco Htprop x Hx Hx'; 
    generalize (tc_dec Hy); intros [z [Hyz [Hzy | Heqzy]]].
      destruct_lin Hlp.
      assert (trans p) as Htp.
        intros e1 e2 e3 H12 H23; apply Htrans with e2; auto.
      generalize Hzy; apply path_co_prop with phi; auto.
        apply irr_trans_ac; auto; intros [x Hx]; apply (Hac x Hx).  
      rewrite Heqzy in Hyz.
        destruct_lin Hlp; generalize Hyz; apply co_prop_irr with phi; auto.
          intros x1 x2 x3 H12 H23; apply Htrans with x2; auto. 
          apply irr_trans_ac; auto. 
            intros x1 x2 x3 H12 H23; apply Htrans with x2; auto. 
            intros [x Hx]; apply (Hac x Hx).
Qed.

End Soundness.

Module Completeness (A:Archi) (dp:Dp). 

  Module S := Soundness A dp.
  Import S AMach AWmm ABasic.

(*Definition Delay := Event_struct -> Execution_witness -> (Rln Event).*)

Definition labels_of_es E X :=
  fun l => (exists w, writes E w /\ (l = d (DW w) \/ l = f (DW w))) \/
           (exists w, exists r, rf X w r /\ (l = d (DR (w,r)) \/ l = f (DR (w,r)))).

Inductive X2p (E:Event_struct) (X:Execution_witness) (*(delay:Delay)*) : Rln Label :=
  | X2p_df : forall w r, 
               labels_of_es E X (f (DR (w,r))) -> 
               X2p E X (*delay*) (d (DR (w,r))) (f (DR (w,r)))
  | X2p_dfw : forall w, 
               labels_of_es E X (f (DW w)) -> 
               X2p E X (*delay*) (d (DW w)) (f (DW w)) 
  | X2p_fencewr : forall w1 w2 r2, (A.fences E) w1 r2 ->
               labels_of_es E X (f (DW w1)) ->
               labels_of_es E X (f (DR (w2,r2))) ->  
               X2p E X (*delay*) (d (DW w1)) (d (DR (w2,r2)))
  | X2p_rf : forall de1 de2, rfe X (evt_of_devt de1) (evt_of_devt de2) ->
               labels_of_es E X (f de1) -> 
               labels_of_es E X (f de2) -> 
               X2p E X (*delay*) (d de1) (d de2)
  | X2p_ws : forall de1 de2, ws X (evt_of_devt de1) (evt_of_devt de2) ->
               labels_of_es E X (f de1) -> 
               labels_of_es E X (f de2) -> 
                X2p E X (*delay*) (f de1) (f de2)
  | X2p_ppo_fences : forall w1 r1 de2, 
               tc (rel_union (A.ppo E) (A.fences E)) r1 (evt_of_devt de2) ->
               labels_of_es E X (f (DR (w1,r1))) ->
               labels_of_es E X (f de2) ->
               X2p E X (*delay*) (f (DR (w1,r1))) (d de2) 
  | X2p_prop : forall de1 de2, tc (A.prop E X) (evt_of_devt de1) (evt_of_devt de2) ->
               labels_of_es E X (f de1) ->
               labels_of_es E X (f de2) ->
               X2p E X (*delay*) (f de1) (f de2).

Lemma ran_q_contrad :
  forall Q e r,
  ~(Q e) ->
  (del_rs Q r) e ->
  False.
Proof.
intros Q e r Hnr [e' Hq]; apply Hnr; auto.
Qed.

Module OEL.
Parameter LE : Rln Label -> Rln Label.
Hypothesis OE : forall (s S:set Label) (r:Rln Label),
  Included _ s S ->
  partial_order r s -> 
  rel_incl r (LE r) /\
  linear_strict_order (LE r) S.
Hypothesis le_lso : forall (s:set Label) (r:Rln Label),
  linear_strict_order r s -> LE r = r.
End OEL.

Lemma oel_tot :
  forall p L,
  partial_order (tc p) L ->
  (forall e1 e2, e1 <> e2 -> 
   L e1 -> L e2 ->
   (OEL.LE (tc p)) e1 e2 \/ (OEL.LE (tc p)) e2 e1).
Proof.
intros p L Hpart.
assert (Included _ L L) as Htl.
  intros l Hl; auto.
generalize (OEL.OE L L (tc p) Htl Hpart);
intros [? Hlin]; destruct_lin Hlin; auto.
Qed.

Lemma oel_trans :
  forall p L,
  partial_order (tc p) L ->
  trans (OEL.LE (tc p)).
Proof.
intros p L Hpart.
assert (Included _ L L) as Htl.
  intros l Hl; auto.
generalize (OEL.OE L L (tc p) Htl Hpart);
intros [? Hlin]; destruct_lin Hlin; auto.
intros x y z Hxy Hyz; apply Htrans with y; auto.
Qed.

Lemma oel_part :
  forall p L,
  partial_order (tc p) L ->
  partial_order (tc (OEL.LE (tc p))) L.
Proof.
intros p L Hpart.
assert (Included _ L L) as Htl.
  intros l Hl; auto.
generalize (OEL.OE L L (tc p) Htl Hpart);
intros [? Hlin]; rewrite trans_tc; [|apply oel_trans with L]; auto.
split; [|split]; destruct_lin Hlin; auto.
Qed.

Lemma oel_ac :
  forall p L,
  partial_order (tc p) L ->
  acyclic (OEL.LE (tc p)).
Proof.
intros p L Hpart.
assert (Included _ L L) as Htl.
  intros l Hl; auto.
generalize (OEL.OE L L (tc p) Htl Hpart);
intros [? Hlin]; destruct_lin Hlin; auto.
intros x Hx; apply Hac with x.
  rewrite trans_tc in Hx; auto.
  apply oel_trans with L; auto.
Qed.

Lemma oel_incl :
  forall p L,
  partial_order (tc p) L ->
  rel_incl (tc p) (OEL.LE (tc p)).
Proof.
intros p L Hpart.
assert (Included _ L L) as Htl.
  intros l Hl; auto.
generalize (OEL.OE L L (tc p) Htl Hpart);
intros [Hi ?]; auto.
Qed.

Lemma oel_dom :
  forall p L x y,
  partial_order (tc p) L ->
  (OEL.LE (tc p)) x y ->
  L x.
Proof.
intros p L x y Hpart Hxy.
assert (Included _ L L) as Htl.
  intros l Hl; auto.
generalize (OEL.OE L L (tc p) Htl Hpart);
intros [? Hlin]; destruct_lin Hlin; auto.
apply Hdr; left; exists y; auto.
Qed.

Lemma oel_ran :
  forall p L x y,
  partial_order (tc p) L ->
  (OEL.LE (tc p)) x y ->
  L y.
Proof.
intros p L x y Hpart Hxy.
assert (Included _ L L) as Htl.
  intros l Hl; auto.
generalize (OEL.OE L L (tc p) Htl Hpart);
intros [? Hlin]; destruct_lin Hlin; auto.
apply Hdr; right; exists x; auto.
Qed.

Lemma oel_udr :
  forall p L,
  partial_order (tc p) L ->
  Included _ (Union _ (dom (OEL.LE (tc p))) (ran (OEL.LE (tc p)))) L.
Proof.
intros p L Hpart ? [x [y Hd] | x [y Hr]].
  apply oel_dom with p y; auto.
  apply oel_ran with p y; auto.
Qed.

Lemma path_dec :
  forall E X l1 l2,
  X2p E X l1 l2 ->
  ( (*d -> f*)
    (exists w, exists r, l1 = d (DR (w,r)) /\ l2 = f (DR (w,r))) \/
 
    (exists w, l1 = d (DW w) /\ l2 = f (DW w)) \/

    (exists de1, exists de2,
     d de1 = l1 /\ d de2 = l2 /\
     (A.fences E) (evt_of_devt de1) (evt_of_devt de2)) \/

    (exists de1, exists de2,
     d de1 = l1 /\ d de2 = l2 /\
     rfe X (evt_of_devt de1) (evt_of_devt de2)) \/

    (exists de1, exists de2, 
     f de1 = l1 /\ f de2 = l2 /\
     ws X (evt_of_devt de1) (evt_of_devt de2)) \/

    (exists w1, exists r1, exists de2, 
     f (DR (w1,r1)) = l1 /\ d de2 = l2 /\
     tc (rel_union (A.ppo E) (A.fences E)) r1 (evt_of_devt de2))    \/

    (exists de1, exists de2, 
     f de1 = l1 /\ f de2 = l2 /\
     tc (A.prop E X) (evt_of_devt de1) (evt_of_devt de2))
   ).
Proof. 
intros E X l1 l2 H12.

  inversion H12 as [w r Hdf | w Hdf | w wr r Hf | e1 e2 Hrf | e1 e2 Hwsf | w1 r1 e2 Hdp | e1 e2 Hprop].
    left; exists w; exists r; split; auto.
    right; left; exists w; split; auto.
    right; right; left; exists (DW w); exists (DR (wr,r)); split; [|split]; simpl; auto.
    right; right; right; left; exists e1; exists e2; split; [|split]; auto.
    right; right; right; right; left; exists e1; exists e2; split; [|split]; auto.
    right; right; right; right; right; left; exists w1; exists r1; exists e2; split; [|split]; auto.
    right; right; right; right; right; right; exists e1; exists e2; split; [|split]; auto.
Qed.

Definition hbl l :=
  (exists w, l = d (DW w)) \/ 
  (exists w, exists r, l = d (DR (w,r)) \/ l = f (DR (w,r))).
Definition copl l :=
  exists w, l = f (DW w).

Lemma hb_co_contrad :
  forall l,
  hbl l -> copl l -> False.    
Proof.
intros l [[w Hldw] | [w [r [Hldr | Hlfr]]]] [w' Hlfw].
  rewrite Hldw in Hlfw; inversion Hlfw.
  rewrite Hldr in Hlfw; inversion Hlfw.
  rewrite Hlfr in Hlfw; inversion Hlfw.
Qed.

Lemma hb_df_eq12 :
  forall l1 l2,
  hbl l1 ->
  (exists w, exists r, d (DR (w, r)) = l1 /\ f (DR (w, r)) = l2) ->
  hbl l2.
Proof.
intros l1 l2 [[w Hldw] | [w [r [Hldr | Hlfr]]]] [w' [r' [Hl1 Hl2]]].
  rewrite <- Hl1 in Hldw; inversion Hldw.
  rewrite <- Hl1 in Hldr; inversion Hldr. 
    rewrite H0 in Hl1; rewrite H1 in Hl1; rewrite H0 in Hl2; rewrite H1 in Hl2;
    rewrite <- Hl2; right; exists w; exists r; auto.
  rewrite <- Hl1 in Hlfr; inversion Hlfr. 
Qed.      

Lemma hb_df_eq21 :
  forall l1 l2,
  hbl l2 ->
  (exists w, exists r, d (DR (w, r)) = l1 /\ f (DR (w, r)) = l2) ->
  hbl l1.
Proof.
intros l1 l2 [[w Hldw] | [w [r [Hldr | Hlfr]]]] [w' [r' [Hl1 Hl2]]].
  rewrite <- Hl2 in Hldw; inversion Hldw.
  rewrite <- Hl2 in Hldr; inversion Hldr. 
  rewrite <- Hl2 in Hlfr; inversion Hlfr. 
    rewrite H0 in Hl1; rewrite H1 in Hl1; rewrite H0 in Hl2; rewrite H1 in Hl2;
    rewrite <- Hl1; right; exists w; exists r; auto.
Qed.   

Lemma co_df_contrad1 :
  forall l l',
  copl l -> 
  (exists w, exists r, d (DR (w,r)) = l /\ f (DR (w,r)) = l') ->
  False.
Proof.
intros l l' [w Hlw] [w' [r' [Hlwr' ?]]].
rewrite Hlw in Hlwr'; inversion Hlwr'.
Qed.

Lemma co_df_contrad2 :
  forall l l',
  copl l -> 
  (exists w, exists r, d (DR (w,r)) = l' /\ f (DR (w,r)) = l) ->
  False.
Proof.
intros l l' [w Hlw] [w' [r' [? Hlwr']]].
rewrite Hlw in Hlwr'; inversion Hlwr'.
Qed.

Lemma tc_path_dec :
  forall E X l1 l2,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  write_serialization_well_formed (events E) (ws X) ->
  wf_devts E ->
  tc (X2p E X) l1 l2 ->
  (hbl l1 /\ hbl l2 /\ tc (AWmm.hb E X) (evt_of_label l1) (evt_of_label l2)) \/

  (copl l1 /\ copl l2 /\ tc (rel_union (co X) (A.prop E X)) (evt_of_label l1) (evt_of_label l2)) \/

  (exists w, exists r, d (DR (w,r)) = l1 /\ f (DR (w,r)) = l2) \/

  (exists w, d (DW w) = l1 /\ f (DW w) = l2) \/

  (hbl l1 /\ copl l2 /\ tc (AWmm.hb E X) (evt_of_label l1) (evt_of_label l2)) \/

  (hbl l1 /\ copl l2 /\ tc (rel_union (co X) (A.prop E X)) (evt_of_label l1) (evt_of_label l2)) \/

  (hbl l1 /\ copl l2 /\ rel_seq (tc (AWmm.hb E X)) (tc (rel_union (co X) (A.prop E X))) (evt_of_label l1) (evt_of_label l2)).
Proof.
intros E X l1 l2 Hwf Hrfwf Hwswf [Hwfdw Hwfdr] H12.
induction H12.

  inversion H.
    right; right; left; exists w; exists r; auto.

    right; right; right; left; exists w; auto.

    left; split; [|split]; auto.
      left; exists w1; auto.
      right; exists w2; exists r2; auto.
      simpl; apply trc_step; right; apply trc_step; right; auto.

    left; split; [|split]; auto.
      left.
        assert (writes E (evt_of_devt de1)) as Hw.
          split.
            apply ABasic.dom_rf_in_events with X (evt_of_devt de2); auto; destruct H0; auto.
            apply ABasic.dom_rf_is_write with E X (evt_of_devt de2); auto; destruct H0; auto.
              destruct Hrfwf as [? [? ?]]; auto.
        generalize (Hwfdw de1 Hw); intros [w Hde]; exists w; rewrite Hde; auto.
      right. 
        assert (reads E (evt_of_devt de2)) as Hr.
          split.
            apply ABasic.ran_rf_in_events with X (evt_of_devt de1); auto; destruct H0; auto.
            apply ABasic.ran_rf_is_read with E X (evt_of_devt de1); auto; destruct H0; auto.
              destruct Hrfwf as [? [? ?]]; auto.
        generalize (Hwfdr de2 Hr); intros [w [r Hde]]; exists w; exists r; rewrite Hde; auto.

      apply trc_step; left; simpl; auto.

    right; left; split; [|split]; auto.
        assert (writes E (evt_of_devt de1)) as Hw.
          split.
            apply ABasic.dom_ws_in_events with X (evt_of_devt de2); auto; auto.
            apply ABasic.dom_ws_is_write with E X (evt_of_devt de2); auto; auto.
        generalize (Hwfdw de1 Hw); intros [w Hde]; exists w; rewrite Hde; auto.
        assert (writes E (evt_of_devt de2)) as Hw.
          split.
            apply ABasic.ran_ws_in_events with X (evt_of_devt de1); auto; auto.
            generalize (ABasic.ran_ws_is_write E X (evt_of_devt de1) (evt_of_devt de2) Hwswf H0); intros [v [l Haw]];
            exists l; exists v; auto.
        generalize (Hwfdw de2 Hw); intros [w Hde]; exists w; rewrite Hde; auto.

      apply trc_step; left; auto.

    left; split; [|split]; auto.
      right; exists w1; exists r1; auto.
      destruct de2. 
        destruct p as [w r]; right; exists w; exists r; auto.
        left; exists e; auto.
      apply trc_step; right; auto.

    right; left; split; [|split]; auto.
      generalize (dom_prop_W E X (evt_of_devt de1) (evt_of_devt de2) H0); intro Hw.
      generalize (Hwfdw de1 Hw); intros [w Hde]; exists w; rewrite Hde; auto.
      generalize (ran_prop_W E X (evt_of_devt de1) (evt_of_devt de2) H0); intro Hw.
      generalize (Hwfdw de2 Hw); intros [w Hde]; exists w; rewrite Hde; auto.

      assert (rel_incl (A.prop E X) (rel_union (ws X) (A.prop E X))) as Hi.
        intros e1 e2 H12; right; auto.
      generalize (tc_incl Hi); intro Hitc; apply Hitc; auto.

  inversion IHtc1 as [hb1 | [co1 | [dfr1 | [dfw1 | [hbdf1 | [codf1 | seq1]]]]]];
  inversion IHtc2 as [hb2 | [co2 | [dfr2 | [dfw2 | [hbdf2 | [codf2 | seq2]]]]]]; clear H12_ H12_0 IHtc1 IHtc2.

    left; destruct hb1 as [hbx [hbz hbxz]]; destruct hb2 as [hbz' [hby hbzy]];
    split; [|split]; auto; apply trc_ind with (evt_of_label z); auto.

    destruct hb1 as [? [hbz ?]]; destruct co2 as [copz ?]; generalize (hb_co_contrad z hbz copz); 
    intro Hf; inversion Hf.

    left; destruct hb1 as [hbx [hbz hbxz]]; split; [|split]; auto.
      apply hb_df_eq12 with z; auto.
      destruct dfr2 as [w [r [Heqz Heqy]]]; rewrite <- Heqz in hbxz; rewrite <- Heqy; auto.

    right; right; right; right; left; destruct hb1 as [hbx [hbz hbxz]];
    destruct dfw2 as [e [hbz' copy]]; split; [|split]; auto; 
      [exists e|rewrite <- copy; rewrite <- hbz' in hbxz; simpl in *|-*]; auto.
    
    right; right; right; right; left; destruct hb1 as [hbx [hbz hbxz]];
    destruct hbdf2 as [hbz' [coy hbzy]]; split; [|split]; auto;
    apply trc_ind with (evt_of_label z); auto.

    right; right; right; right; right; right; destruct hb1 as [hbx [hbz hbxz]];
    destruct codf2 as [? [coy cozy]]; split; [|split]; auto;
    exists (evt_of_label z); auto.

    right; right; right; right; right; right; destruct hb1 as [hbx [hbz hbxz]];
    destruct seq2 as [? [coy [e [Hze Hey]]]]; split; [|split]; auto;
    exists e; auto; split; auto; apply trc_ind with (evt_of_label z); auto.

    destruct co1 as [? [copz ?]]; destruct hb2 as [hbz ?]; generalize (hb_co_contrad z hbz copz); 
    intro Hf; inversion Hf.

    right; left; destruct co1 as [cox [coz coxz]]; destruct co2 as [coz' [coy cozy]]; 
    split; [|split]; auto; apply trc_ind with (evt_of_label z); auto.

    destruct co1 as [? [coz ?]]; generalize (co_df_contrad1 z y coz dfr2); intro Hf; inversion Hf.

    destruct co1 as [? [[? Hfz] ?]]; destruct dfw2 as [? [Hdz ?]];
    rewrite Hfz in Hdz; inversion Hdz.

    destruct co1 as [? [coplz ?]]; destruct hbdf2 as [hbz ?];
    generalize (hb_co_contrad z hbz coplz); intro Ht; inversion Ht.

    destruct co1 as [? [coplz ?]]; destruct codf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct co1 as [? [coplz ?]]; destruct seq2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    left; destruct hb2 as [hbz [hby hbzy]]; split; [|split]; auto.
      apply hb_df_eq21 with z; auto.
      destruct dfr1 as [w [r [Heqx Heqz]]]; rewrite <- Heqz in hbzy; rewrite <- Heqx; auto.

    destruct co2 as [coz ?]; generalize (co_df_contrad2 z x coz dfr1); intro Hf; inversion Hf.

    destruct dfr1 as [? [? [? Hz]]]; destruct dfr2 as [? [? [Hz' ?]]]; rewrite <- Hz in Hz'; inversion Hz'.

    destruct dfr1 as [? [? [? Hz]]]; destruct dfw2 as [? [Hz' ?]]; rewrite <- Hz in Hz'; inversion Hz'.

    destruct dfr1 as [e1 [e2 [Hx Hz]]];
    destruct hbdf2 as [? [coply Hzy]];
    rewrite <- Hz in Hzy; rewrite <- Hx;
    right; right; right; right; left; simpl; split; auto; 
    right; exists e1; exists e2; auto.

    destruct dfr1 as [e1 [e2 [Hx Hz]]];
    destruct codf2 as [? [coply Hs]];
    rewrite <- Hz in Hs; rewrite <- Hx;
    right; right; right; right; right; left; split; [|split]; auto;
    right; exists e1; exists e2; auto.

    destruct dfr1 as [e1 [e2 [Hx Hz]]];
    destruct seq2 as [? [coply Hs]];
    rewrite <- Hz in Hs; rewrite <- Hx;
    right; right; right; right; right; right; split; [|split]; auto;
    right; exists e1; exists e2; auto.

    assert (copl z) as coplz.
      destruct dfw1 as [e [? Hfz]]; exists e; auto.
    destruct hb2 as [hbz ?]; generalize (hb_co_contrad z hbz coplz); intro Ht; inversion Ht.

    destruct dfw1 as [e [Hx Hz]];
    destruct co2 as [? [coy Hs]];
    rewrite <- Hz in Hs; rewrite <- Hx;
    right; right; right; right; right; left; split; [|split]; auto;
    left; exists e; auto.

    assert (copl z) as coplz.
      destruct dfw1 as [e [? Hfz]]; exists e; auto.
    assert (hbl z) as hblz.
      destruct dfr2 as [e1 [e2 [Hdz ?]]]; right; exists e1; exists e2; auto.
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.   

    assert (copl z) as coplz.
      destruct dfw1 as [e [? Hfz]]; exists e; auto.
    assert (hbl z) as hblz.
      destruct dfw2 as [e [Hdz ?]]; left; exists e; auto.
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    assert (copl z) as coplz.
      destruct dfw1 as [e [? Hfz]]; exists e; auto.
    destruct hbdf2 as [hblz ?].
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    assert (copl z) as coplz.
      destruct dfw1 as [e [? Hfz]]; exists e; auto.
    destruct codf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    assert (copl z) as coplz.
      destruct dfw1 as [e [? Hfz]]; exists e; auto.
    destruct seq2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.    

    destruct hbdf1 as [? [coplz ?]];
    destruct hb2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct hbdf1 as [? [coplz hbxz]];
    destruct co2 as [? [coply cozy]];
    right; right; right; right; right; right; split; [|split]; auto;
    exists (evt_of_label z); auto.

    assert (hbl z) as hblz.
      destruct dfr2 as [e1 [e2 [Hz ?]]]; right; exists e1; exists e2; auto.
    destruct hbdf1 as [? [coplz ?]];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    assert (hbl z) as hblz.
      destruct dfw2 as [e [Hz ?]]; left; exists e; auto.
    destruct hbdf1 as [? [coplz ?]];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct hbdf1 as [? [coplz ?]];
    destruct hbdf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.   

    destruct hbdf1 as [? [coplz ?]];
    destruct codf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct hbdf1 as [? [coplz ?]];
    destruct seq2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct codf1 as [? [coplz ?]];
    destruct hb2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct codf1 as [Hx [? Hs1]];
    destruct co2 as [? [Hy Hs2]];
    right; right; right; right; right; left;
    split; [|split]; auto;
    apply trc_ind with (evt_of_label z); auto.

    assert (hbl z) as hblz.
      destruct dfr2 as [e1 [e2 [Hz ?]]]; right; exists e1; exists e2; auto.
    destruct codf1 as [? [coplz ?]];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    assert (hbl z) as hblz.
      destruct dfw2 as [e [Hz ?]]; left; exists e; auto.
    destruct codf1 as [? [coplz ?]];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct codf1 as [? [coplz ?]];
    destruct hbdf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct codf1 as [? [coplz ?]];
    destruct codf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct codf1 as [? [coplz ?]];
    destruct seq2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct seq1 as [? [coplz ?]];
    destruct hb2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct seq1 as [hbx [coplz [e [Hxe Hez]]]];
    destruct co2 as [? [coy Hco]];
    right; right; right; right; right; right; split; [|split]; auto;
    exists e; auto; split; auto; apply trc_ind with (evt_of_label z); auto.

    assert (hbl z) as hblz.
      destruct dfr2 as [e1 [e2 [Hz ?]]]; right; exists e1; exists e2; auto.
    destruct seq1 as [? [coplz ?]];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    assert (hbl z) as hblz.
      destruct dfw2 as [e [Hz ?]]; left; exists e; auto.
    destruct seq1 as [? [coplz ?]];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct seq1 as [? [coplz ?]];
    destruct hbdf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct seq1 as [? [coplz ?]];
    destruct codf2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.

    destruct seq1 as [? [coplz ?]];
    destruct seq2 as [hblz ?];
    generalize (hb_co_contrad z hblz coplz); intro Ht; inversion Ht.
Qed.
    
Lemma ac_ghb_implies_ac_X2p :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  acyclic (X2p E X).
Proof.
intros E X Hwf Hv Hwfd x Hx.
destruct_valid Hv.
assert (rfmaps_well_formed E (events E) (rf X)) as Hwfrf.
  split; auto.
assert (write_serialization_well_formed (events E) (ws X)) as Hwswf.
  split; auto.

generalize (tc_path_dec E X x x Hwf Hwfrf Hwswf Hwfd Hx); 
intros [[? [? Hhb]] | [[? [? Hprop]] | Hrest]].

  apply Hth with (evt_of_label x); auto.
  apply Hvalid with (evt_of_label x); auto.
  inversion Hrest as [Hdr | [Hdw | [Hhb | [Hco | Hseq]]]]; clear Hrest.
    destruct Hdr as [w [r [Hd Hf]]]; rewrite <- Hd in Hf; inversion Hf.
    destruct Hdw as [w [Hd Hf]]; rewrite <- Hd in Hf; inversion Hf.
    destruct Hhb as [hblx [coplx ?]];
    generalize (hb_co_contrad x hblx coplx); intro Ht; inversion Ht.
    destruct Hco as [hblx [coplx ?]];
    generalize (hb_co_contrad x hblx coplx); intro Ht; inversion Ht.
    destruct Hseq as [hblx [coplx ?]];
    generalize (hb_co_contrad x hblx coplx); intro Ht; inversion Ht.
Qed.

Lemma label_implies_evt :
  forall E X l de,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  labels_of_es E X l ->
  l = d de \/ l = f de ->
  events E (evt_of_devt de).
Proof.
intros E X l de Hwf Hrfwf [Hw | Hr] Hor.

  destruct Hw as [w [Hw [Hdw | Hfw]]]; inversion Hor as [Hd | Hf]; clear Hor.
    rewrite Hdw in Hd; inversion Hd; simpl; destruct Hw; auto.
    rewrite Hdw in Hf; inversion Hf.
    rewrite Hfw in Hd; inversion Hd.
    rewrite Hfw in Hf; inversion Hf; simpl; destruct Hw; auto.

  destruct Hr as [w [r [Hrf [Hdr | Hfr]]]]; inversion Hor as [Hd | Hf]; clear Hor.
    rewrite Hdr in Hd; inversion Hd; simpl; apply ABasic.ran_rf_in_events with X w; auto.
    rewrite Hdr in Hf; inversion Hf.
    rewrite Hfr in Hd; inversion Hd.
    rewrite Hfr in Hf; inversion Hf; simpl; apply ABasic.ran_rf_in_events with X w; auto.
Qed.

Lemma dom_X2p_is_label :
  forall E X l l',
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) ->
  rfmaps_well_formed E (events E) (rf X) ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  tc (X2p E X) l l' ->
  labels_of_es E X l.
Proof.
intros E X l l' Hwf Hwfws Hrfwf Hwfl Hwfrfl Hll'.

induction Hll' as [x y Hxy|]; auto.

generalize Hwfl; intros Hwfl'; destruct Hwfl' as [? [? [? Hldf]]];
inversion Hxy as [? | ? | ? | ? | ? | ? | ?]; auto.
Qed.

Lemma ran_X2p_is_label :
  forall E X l l',
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) ->
  rfmaps_well_formed E (events E) (rf X) ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  tc (X2p E X) l l' ->
  labels_of_es E X l'.
Proof.
intros E X l l' Hwf Hwfws Hrfws Hwfl Hwfrfl Hll'.
induction Hll' as [x y Hxy|]; auto.

generalize Hwfl; intros Hwfl'; destruct Hwfl' as [? [? [? Hldf]]];
inversion Hxy as [? | ? |? | ? | ? | ? | ?]; auto.
Qed.

Lemma wfl_es :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X).
Proof.
intros E X Hwf Hv; split; [|split; [|split]].
  
  split; intros w [Hw|Hr].
    destruct Hw as [w' [Hw' [Heq | Heq]]]; inversion Heq; auto.
    destruct Hr as [w' [r' [? [Heq | Heq]]]]; inversion Heq.
    destruct Hw as [w' [Hw' [Heq | Heq]]]; inversion Heq; auto.
    destruct Hr as [w' [r' [? [Heq | Heq]]]]; inversion Heq.

  split; intros w r [Hw|Hr].
    destruct Hw as [w' [Hw' [Heq | Heq]]]; inversion Heq.
    destruct Hr as [w' [r' [? [Heq | Heq]]]]; inversion Heq; auto.
      destruct_valid Hv; apply Hrf_cands; auto.
    destruct Hw as [w' [Hw' [Heq | Heq]]]; inversion Heq.
    destruct Hr as [w' [r' [? [Heq | Heq]]]]; inversion Heq; auto.
      destruct_valid Hv; apply Hrf_cands; auto.

  intros w Hw; left; exists w; split; auto.

  intros de [Hw|Hr].
    destruct Hw as [w [Hw [Hl|Hl]]]; left; exists w; inversion Hl; auto.
    destruct Hr as [w [r [Hrf [Hl|Hl]]]]; right; exists w; exists r; inversion Hl; auto.
Qed.
    
Lemma wfl_rf_es :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_rf_labels E (labels_of_es E X).
Proof.
intros E X Hwf Hv; split.

  intros r Hr; destruct_valid Hv; generalize (Hrf_init r Hr); intros [w [Hew Hrf]];
  exists w; split; auto.
    right; exists w; exists r; split; auto. 

  split; intros r w1 w2 [Hl1 | Hl1] [Hl2 | Hl2].
    destruct Hl1 as [w1' [Hw1' [Hl1 | Hl1]]]; inversion Hl1.
    destruct Hl1 as [w1' [Hw1' [Hl1 | Hl1]]]; inversion Hl1.
    destruct Hl2 as [w2' [Hw2' [Hl2 | Hl2]]]; inversion Hl2.

    destruct Hl1 as [w1' [r1' [Hrf1 [Hl1 | Hl1]]]]; destruct Hl2 as [w2' [r2' [Hrf2 [Hl2 | Hl2]]]];
    inversion Hl1; inversion Hl2.
      rewrite <- H0 in * |- *; rewrite H1 in * |- *; rewrite <- H2 in * |- *; rewrite <- H3 in * |- *; auto.
      destruct_valid Hv; apply Hrf_uni with r1'; auto.

    destruct Hl1 as [w1' [Hw1' [Hl1 | Hl1]]]; inversion Hl1.
    destruct Hl1 as [w1' [Hw1' [Hl1 | Hl1]]]; inversion Hl1.
    destruct Hl2 as [w2' [Hw2' [Hl2 | Hl2]]]; inversion Hl2.

    destruct Hl1 as [w1' [r1' [Hrf1 [Hl1 | Hl1]]]]; destruct Hl2 as [w2' [r2' [Hrf2 [Hl2 | Hl2]]]];
    inversion Hl1; inversion Hl2.
      rewrite <- H0 in * |- *; rewrite H1 in * |- *; rewrite <- H2 in * |- *; rewrite <- H3 in * |- *; auto.
      destruct_valid Hv; apply Hrf_uni with r1'; auto.
Qed.

Lemma tc_X2p_partial_order :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  partial_order (tc (X2p E X)) (labels_of_es E X).
Proof.
intros E X Hwf Hv Hwfd; generalize Hv; intro Hv';
  generalize (wfl_es E X Hwf Hv); intro Hwfl;
  generalize (wfl_rf_es E X Hwf Hv); intro Hwfrfl;
  destruct_valid Hv; split; [|split].
  intros ? [l [l' Hd] | l [l' Hr]].
    apply dom_X2p_is_label with l'; auto; split; auto.
    apply ran_X2p_is_label with l'; auto; split; auto.

  intros x1 x2 x3 [H12 H23]; apply trc_ind with x2; auto.

  intros x; apply ac_ghb_implies_ac_X2p; auto.
Qed.

Lemma wfl_le2 :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  ((forall l : Label, labels_of_es E X l -> events E (evt_of_label l))).
Proof.
intros E X Hwf Hv l [Hw | Hr]; destruct_valid Hv.
  destruct Hw as [w [[Hew ?] [Hl | Hl]]]; rewrite Hl; auto.
  destruct Hr as [w [r [Hrf [Hl | Hl]]]]; rewrite Hl; simpl;
  apply ABasic.ran_rf_in_events with X w; auto; split; auto.
Qed.

Lemma oel_df :
  forall E X w r,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DR (w,r))) -> OEL.LE (tc (X2p E X)) (d (DR (w,r))) (f (DR (w,r))).
Proof.
intros E X w r Hwf Hv Hwfd Hwfl Hl.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
apply Hi; apply trc_step; apply X2p_df; auto.
Qed.

Lemma in_order_implies_mem_or_buff_state_d :
  forall E X n s0 s1 w r phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) -> 
  labels_of_es E X (f (DW w)) -> labels_of_es E X (f (DR (w,r))) ->
  rfe X w r ->
  machine E (pred (OEL.LE (tc (X2p E X))) (d (DR (w,r)))) (labels_of_es E X) (d (DR (w,r))) n phi (Some s0) (Some s1) ->
  ((B s1) w).
Proof. 
intros E X n s0 s1 w r phi Hwf Hv Hwfd Hwfl Hlfw Hlfwr Hrf Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.

assert (labels_of_es E X (d (DW w))) as Hldw.
  destruct Hwfl as [? [? [? Hldf]]]; apply Hldf; auto.
assert (labels_of_es E X (d (DR (w,r)))) as Hldwr.
  destruct Hwfl as [? [? [? Hfd]]]; apply Hfd; auto.

assert (d (DW w) <> d (DR (w,r))) as Hdiff.
  intro Hfeq; inversion Hfeq as [Heq].
generalize (Htotp (d (DW w)) (d (DR (w,r))) Hdiff Hldw Hldwr); intro Hor;
inversion Hor as [Hpwr | Hprw]; clear Hor.

  assert (loc w = loc r) as Heql.
    assert (rfmaps_well_formed E (events E) (rf X)) as Hwfrf.
      destruct_valid Hv; split; auto.
      apply rf_implies_same_loc2 with E X; auto. split; auto.
        destruct_valid Hv; split; auto. destruct Hrf; auto.

  generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
  apply in_order_implies_in_buff with E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (d (DR (w,r))) n s0 (d (DR (w,r))) phi; auto.
  apply oel_udr; auto.
  apply oel_ac with (labels_of_es E X); auto. 
  apply wfl_e; auto.

  exists (pred (OEL.LE (tc (X2p E X))) (d (DR (w, r)))); split; [|split; [|split]]; auto. 
    apply td_tpred; auto. intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

  assert (Included _ (labels_of_es E X) (labels_of_es E X)) as Htl.
    intros e He; auto.
  generalize (OEL.OE (labels_of_es E X) (labels_of_es E X) (tc (X2p E X)) Htl Hpart);
    clear Htl; intros [Hil Hl].
  destruct_lin Hl.
  assert (trans (OEL.LE (tc (X2p E X)))) as Htr.
    intros x1 x2 x3 H12 H23; apply Htrans with x2; auto.
  assert (acyclic (OEL.LE (tc (X2p E X)))) as Hacy.
    intros e He. 
      rewrite trans_tc in He; auto; apply (Hac e He).
    assert (exists dr : Rln Label, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (d (DR (w, r)))) /\
      (~(exists l' : Label,
         tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
         tc (OEL.LE (tc (X2p E X))) l' (d (DR (w, r)))) \/ Last.last dr = d (DR (w,r))) /\
    machine E dr (labels_of_es E X) (d (DR (w, r))) n phi (Some s0) (Some s1)) as Hed.
      exists (pred (OEL.LE (tc (X2p E X))) (d (DR (w,r)))); split; [|split; [|split]]; auto.
        apply td_tpred; auto.
        intros e1 e2 H12; auto.
        left; apply Last.no_interv_last; auto; intros e1 e2 H12; auto.                 
     
  assert (forall l : Label, labels_of_es E X l -> events E (evt_of_label l)) as Hle.
    apply wfl_le2; auto.
  generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.

  assert (OEL.LE (tc (X2p E X)) (d (DW w)) (d (DR (w, r)))) as Hwr.
    apply Hi; apply trc_step. 
    apply X2p_rf; auto.  

  assert (~ (exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (d (DR (w, r))) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (d (DR (w, r)))) \/
  d (DR (w, r)) = d (DR (w, r))) as Hni.
    auto.
  assert (OEL.LE (tc (X2p E X)) (d (DR (w,r))) (d (DW w)) \/ (d (DR (w,r))) = d (DW w)) as Hor.
    left; auto.

  generalize (in_order_implies_in_buff E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (d (DR (w,r))) n s0 s1 w (d (DR (w,r))) phi Hwfl Hdr Htr Hacy Htotp Hle Hwr Hwr (*Hor*) Hlfw (*Hdf*) Hni Hed); 
  intros. 
       
    auto.
Qed. 

Lemma in_order_implies_mem_or_buff_state :
  forall E X n s0 s1 w r phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) -> 
  labels_of_es E X (f (DW w)) -> labels_of_es E X (f (DR (w,r))) ->
  rf X w r ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w,r)))) (labels_of_es E X) (f (DR (w,r))) n phi (Some s0) (Some s1) ->
  (po_iico E w r \/ (B s1) w).
Proof. 
intros E X n s0 s1 w r phi Hwf Hv Hwfd Hwfl Hlfw Hldwr Hrf Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.

assert (labels_of_es E X (d (DW w))) as Hldw.
  destruct Hwfl as [? [? [? Hldf]]]; apply Hldf; auto.

assert (d (DW w) <> f (DR (w,r))) as Hdiff.
  intro Hfeq; inversion Hfeq as [Heq].
generalize (Htotp (d (DW w)) (f (DR (w,r))) Hdiff Hldw Hldwr); intro Hor;
inversion Hor as [Hpwr | Hprw]; clear Hor.

  assert (loc w = loc r) as Heql.
    assert (rfmaps_well_formed E (events E) (rf X)) as Hwfrf.
      destruct_valid Hv; split; auto.
      apply rf_implies_same_loc2 with E X; auto. split; auto.
        destruct_valid Hv; split; auto. 

  generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
  right; apply in_order_implies_in_buff with E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DR (w,r))) n s0 (f (DR (w,r))) phi; auto.
  apply oel_udr; auto.
  apply oel_ac with (labels_of_es E X); auto. 
  apply wfl_e; auto.

  exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w, r)))); split; [|split; [|split]]; auto. 
    apply td_tpred; auto. intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

  assert (Included _ (labels_of_es E X) (labels_of_es E X)) as Htl.
    intros e He; auto.
  generalize (OEL.OE (labels_of_es E X) (labels_of_es E X) (tc (X2p E X)) Htl Hpart);
    clear Htl; intros [Hil Hl].
  destruct_lin Hl.
  assert (trans (OEL.LE (tc (X2p E X)))) as Htr.
    intros x1 x2 x3 H12 H23; apply Htrans with x2; auto.
  assert (acyclic (OEL.LE (tc (X2p E X)))) as Hacy.
    intros e He. 
      rewrite trans_tc in He; auto; apply (Hac e He).
    assert (exists dr : Rln Label, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (f (DR (w, r)))) /\
      (~(exists l' : Label,
         tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
         tc (OEL.LE (tc (X2p E X))) l' (f (DR (w, r)))) \/ Last.last dr = f (DR (w,r))) /\
    machine E dr (labels_of_es E X) (f (DR (w, r))) n phi (Some s0) (Some s1)) as Hed.
      exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w,r)))); split; [|split; [|split]]; auto.
        apply td_tpred; auto.
        intros e1 e2 H12; auto.
        left; apply Last.no_interv_last; auto; intros e1 e2 H12; auto.                 
     
  assert (forall l : Label, labels_of_es E X l -> events E (evt_of_label l)) as Hle.
    apply wfl_le2; auto.
  generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.

  assert (po_iico E w r \/ rfe X w r) as Hor.
    destruct (eqProc_dec (proc_of w) (proc_of r)) as [Hp|Hnp].
      assert (w <> r) as Hdwr.
        destruct_valid Hv;
        intro Heq; rewrite Heq in Hrf;
        generalize (ABasic.dom_rf_is_write E X r r Hrf_cands Hrf); intros [? [? Hwr]];
        generalize (ABasic.ran_rf_is_read E X r r Hrf_cands Hrf); intros [? [? Hrr]];
        rewrite Hwr in Hrr; inversion Hrr.
      assert (Ensembles.In Event (events E) w) as Hew.
        apply ABasic.dom_rf_in_events with X r; auto.
        destruct_valid Hv; split; auto.
      assert (Ensembles.In Event (events E) r) as Her.
        apply ABasic.ran_rf_in_events with X w; auto.
        destruct_valid Hv; split; auto.

      left; generalize (ABasic.same_proc_implies_po Hwf Hp Hdwr Hew Her).
      intros [|Hporw]; auto.
      assert (po_loc_llh E r w) as Hllh.
        destruct_valid Hv; split; [|split]; auto.
        apply sym_eq.
        apply ABasic.rf_implies_same_loc2 with E X; auto.
        split; split; auto.
        intros [Hr [? [? [? Har]]]].
        generalize (ABasic.dom_rf_is_write E X w r Hrf_cands Hrf);
        intros [? [? Haw]]; rewrite Haw in Har; inversion Har.
      destruct_valid Hv; generalize (Huni r w Hllh); intro Hn.
      assert (AWmm.com' E X w r) as Hy.
        left; left; left; left; auto.
      contradiction.
      right; split; auto.

  inversion Hor as [Hpo | Hrfe]; clear Hor; auto; right.

  assert (OEL.LE (tc (X2p E X)) (d (DW w)) (f (DR (w, r)))) as Hwr.
    apply Hi; apply trc_ind with (d (DR (w,r))); apply trc_step. 
    apply X2p_rf; auto. apply X2p_df; auto. 

  assert (~ (exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (f (DR (w, r))) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (f (DR (w, r)))) \/
  f (DR (w, r)) = f (DR (w, r))) as Hni.
    auto.
  assert (OEL.LE (tc (X2p E X)) (f (DR (w,r))) (d (DW w)) \/ (f (DR (w,r))) = d (DW w)) as Hor.
    left; auto.

  generalize (in_order_implies_in_buff E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DR (w,r))) n s0 s1 w (f (DR (w,r))) phi Hwfl Hdr Htr Hacy Htotp Hle Hwr Hwr (*Hor*) Hlfw (*Hdf*) Hni Hed); 
  intros. 
       
    auto.
Qed. 

Lemma ioipobs :
  forall E X n s0 s1 w r phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X) -> 
  wf_devts E ->
  labels_of_es E X (f (DW w)) -> labels_of_es E X (f (DR (w,r))) ->
  rf X w r ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w,r)))) (labels_of_es E X) (f (DR (w,r))) n phi (Some s0) (Some s1) ->
  bin (Union _ ((B s1)) (fun e => po_loc E e r /\ e = w)) w  = true.
Proof.
intros E X n s0 s1 w r phi Hwf Hv Hwfd  Hwfl Hlfw Hldwr Hrf Hm.
case_eq (bin (Union Event ((B s1)) (fun e : Event => po_loc E e r /\ e = w)) w); intro Hu; auto.
generalize (nbin_nIn (Union Event ((B s1)) (fun e : Event => po_loc E e r /\ e = w)) w Hu); intro Hn.
assert False as Ht. 
  apply Hn.
  generalize (in_order_implies_mem_or_buff_state E X n s0 s1 w r phi Hwf Hv Hwfl Hwfd Hlfw Hldwr Hrf Hm);
  intros [Hpo | Hb].
    right; split; auto.
      split; auto. 
      apply ABasic.rf_implies_same_loc2 with E X; auto.
        destruct_valid Hv; split; split; auto.
      left; auto.
inversion Ht.
Qed.

Lemma rf_p2X_X2p :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  rf (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)) = rf X.
Proof.
intros E X Hwf Hv Hwfl Hwfrfl; apply ext_rel; intros x y; split; intro Hxy.

  simpl in Hxy; unfold p2rf in Hxy.
  assert (reads E y) as Hry.    
    destruct Hxy as [[? [? [l [? [[v Hry] ?]]]]] ?].
    split; auto; exists l; exists v; auto.
  destruct_valid Hv; generalize (Hrf_init y Hry); intros [w [Hew Hrf]].
  destruct (eqEv_dec x w) as [Heq | Hneq]; subst; auto.
  destruct Hwfrfl as [? [? Huniw]].
  assert (labels_of_es E X (f (DR (w,y)))) as Hlfw.
    right; exists w; exists y; split; auto.
  assert (labels_of_es E X (f (DR (x,y)))) as Hlfx.
    destruct Hxy; auto.
  generalize (Huniw y w x Hlfw Hlfx); auto;
  intro; assert False as Ht.
    apply Hneq; auto.
  inversion Ht.

  simpl; unfold p2rf; split. 
    destruct_valid Hv; generalize (Hrf_cands x y Hxy); intro Hrfm; auto.
    right; exists x; exists y; split; auto.
Qed.

Lemma ws_p2X_X2p :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X) -> 
  wf_devts E ->
  ws (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)) = ws X.
Proof.
intros E X Hwf Hv Hwfl Hwfd; apply ext_rel; intros x y; split; intro Hxy.

  simpl in Hxy; unfold p2ws in Hxy.
  destruct Hxy as [Hwx [Hwy [Hl [l1 [l2 [Hl1 [Hl2 H12]]]]]]].
  generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
  
  assert (x <> y) as Hdiff.
    intro Heq; rewrite Heq in Hl1; rewrite Hl1 in H12; rewrite Hl2 in H12.
    apply Hacp with (f (DW y)); apply trc_step; auto.

  assert ((writes_to_same_loc_l (events E) (loc x)) x) as Hwwx.
    destruct Hwx as [? [lx [vx Hax]]]; split; auto.
    exists vx; unfold loc; rewrite Hax; auto.

  assert ((writes_to_same_loc_l (events E) (loc x)) y) as Hwwy.
    destruct Hwy as [? [ly [vy Hay]]]; split; auto.
    rewrite Hl; exists vy; unfold loc; rewrite Hay; auto.

  generalize Hv; intro Hv'; destruct_valid Hv'; 
    generalize (Hws_tot (loc x)); intro Hlin; destruct_lin Hlin.
  generalize (Htot x y Hdiff Hwwx Hwwy); intros [[Hxy?] | [Hyx ?]]; auto.
  assert (OEL.LE (tc (X2p E X)) l2 l1) as H21.
    rewrite Hl1; rewrite Hl2.
    generalize (oel_incl (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hi;
    apply Hi; apply trc_step.
      destruct Hwfl as [? [? [Hw ?]]];   
      apply X2p_ws; auto.

    assert (tc (OEL.LE (tc (X2p E X))) l1 l1) as Hc.
      apply trc_ind with l2; auto; apply trc_step; auto.
    generalize (Hacp l1 Hc); intro Ht; inversion Ht.

  simpl; unfold p2ws.
  generalize Hv; intro Hv'; destruct_valid Hv'.
  generalize (Hws_cands x y Hxy); intros [l [[? [vx Hwx]] [? [vy Hwy]]]].
    split; split; auto.
      exists l; exists vx; auto.
      split; auto; exists l; exists vy; auto.
        split. unfold loc; rewrite Hwx; rewrite Hwy; auto.
          exists (f (DW x)); exists (f (DW y)); split; [|split]; auto.
              destruct Hwfl as [? [? [Hw ?]]]; 
              generalize (oel_incl (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hi;
              apply Hi; apply trc_step; apply X2p_ws; auto.
                  apply Hw; auto. split; auto; exists l; exists vx; auto.
                  apply Hw; auto. split; auto; exists l; exists vy; auto.
Qed.

Lemma p2X_X2p :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) -> 
  wf_devts E ->
  p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X) = X.
Proof.
intros E X Hwf Hv Hwfl Hwfrfl Hwfd.
assert (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X) = 
  mkew (ws (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X) )) 
    (rf (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)) )) as Heq.
  simpl; auto.
rewrite Heq; rewrite ws_p2X_X2p; auto; rewrite rf_p2X_X2p; simpl; auto.
destruct X; simpl; auto.
Qed.

Lemma in_order_implies_rs_state :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DR (w1,r1))) ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1) ->
  bin ((Rs s1)) r1 = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfrfl Hlwr1 Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_ac (X2p E X) (labels_of_es E X) Hpart); intro Hac.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htot.
assert (OEL.LE (tc (X2p E X)) (f (DR (w1,r1))) (f (DR (w1,r1))) \/ f (DR (w1,r1)) = f (DR (w1,r1))) as Hor.
  auto.
assert (exists d : Rln Label, trans d /\ rel_incl d (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) /\ 
        ~(exists l' : Label,
          tc (OEL.LE (tc (X2p E X))) (Last.last d) l' /\
          tc (OEL.LE (tc (X2p E X))) l' (f (DR (w1, r1)))) /\
        machine E d (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1)) as Hed.
  exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))); split; [|split; [|split]]; auto.
    apply td_tpred; auto; intros e1 e2 H12; auto.
    intros e1 e2 H12; auto.
    apply Last.no_interv_last; auto; intros e1 e2 H12; auto.
assert (Included Label
    (Union Label (dom (OEL.LE (tc (X2p E X))))
       (ran (OEL.LE (tc (X2p E X))))) (labels_of_es E X)) as Hudr.
  apply oel_udr; auto.
assert (~ (exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (f (DR (w1, r1))) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (f (DR (w1, r1)))) \/
  f (DR (w1, r1)) = f (DR (w1, r1))) as Hni.
  auto.
assert (OEL.LE (tc (X2p E X)) (d (DR (w1,r1))) (f (DR (w1,r1)))) as Hpdf.
  generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi;
  apply Hi; apply trc_step; apply X2p_df; auto.
generalize (in_order_implies_in_rs E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DR (w1,r1))) n s0 s1 (f (DR (w1,r1))) w1 r1 (*Hdf*) phi Hudr Htrans Hac Htot Hwfrfl Hlwr1 (*Hdf*) Hpdf Hpdf (*Hor*) Hni Hed);
  intros Hran.
apply In_bin; auto.
Qed.

Lemma pred_pred :
  forall (p:Rln Label) l l',
  trans p ->
  p l' l ->
  pred (pred p l) l' = pred p l'.
Proof.
intros p l l' Htp Hl'l; apply ext_rel; intros x y; split; 
  intros [H1 H2]; split; auto.
    destruct H1; auto.
    destruct H2; auto.

    split; auto.
        apply Htp with l'; auto.
    split; auto.
Qed.

Lemma same_last_eq :
  forall L d p ld lp,
  L lp -> L ld ->
  rel_incl d p ->
  trans p ->
  (forall l1 l2, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->
  Last.last (pred p lp) = Last.last (pred d ld) ->
  ld = lp.
Proof.
intros L d p ld lp Hlp Hld Hi Htp Htotp Heql.
destruct (eqLabel_dec ld lp) as [|Hdiff]; auto.
assert (p ld lp \/ p lp ld) as Hor.
  apply Htotp; auto.

inversion Hor as [Hdp | Hpd]; clear Hor.
  assert (~(exists l', p (Last.last (pred p lp)) l' /\ p l' lp)) as Hn.
    rewrite <- trans_tc with Label p; auto.
    apply Last.no_interv_last; auto; intros x y Hxy; auto.
      rewrite <- trans_tc with Label p; auto.
  assert (exists l', p (Last.last (pred p lp)) l' /\ p l' lp) as Hy.
    rewrite Heql; exists ld; split; auto.
      apply Hi. 
      assert (Last.last (pred d ld) = Last.last (pred d ld)) as Heq.
        auto.
      generalize (Last.last_in_ran (pred d ld) (Last.last (pred d ld)) Heq); intros [x [? ?]]; auto.    
  contradiction.

  assert (~(exists l', p (Last.last (pred d ld)) l' /\ p l' ld)) as Hn.
    rewrite <- trans_tc with Label p; auto.
    apply Last.no_interv_last; auto; intros x y Hxy; auto.
  assert (exists l', p (Last.last (pred d ld)) l' /\ p l' ld) as Hy.
    rewrite <- Heql; exists lp; split; auto.
      assert (Last.last (pred p lp) = Last.last (pred p lp)) as Heq.
        auto.
      generalize (Last.last_in_ran (pred p lp) (Last.last (pred p lp)) Heq); intros [x [? ?]]; auto.
  contradiction.  
Qed.

Lemma ws_pp_p :
  forall E p pp L e el,
  rel_incl pp p ->
  ws (p2X E pp L) e el ->
  ws (p2X E p L) e el.
Proof.
intros E p pp L e el Hip [? [? [? [l1 [l2 [? [? H12]]]]]]];
split; [|split; [|split]]; auto.
exists l1; exists l2; split; [|split]; auto; apply Hip; auto.
Qed.

Lemma prop_incl_monot :
  forall E p pp L e1 e2,
  rel_incl pp p ->
  (A.prop E (p2X E pp L)) e1 e2 ->
  (A.prop E (p2X E p L)) e1 e2.
Proof.
intros E p pp L e1 e2 Hi H12; auto.
  apply A.wit_incl with (p2X E pp L); auto.
Qed.

Lemma prop_wit_incl :
  forall E X X' e1 e2,
  (forall e1 e2, (rf X) e1 e2 -> (rf X') e1 e2) ->
  (A.prop E X) e1 e2 ->
  (A.prop E X') e1 e2.
Proof.
intros E X X' e1 e2 Hirf Htc.
  apply A.wit_incl with X; auto.
Qed.

Lemma step_monot :
  forall E p pp L s1 s2 l phi,
  rel_incl pp p ->
  step E pp L (Some s1) l phi = s2 ->
  step E p L (Some s1) l phi = s2.  
Proof.
intros E p pp L s1 s2 l phi Hi Hs.
case_eq l; intros de Hl; 
rewrite Hl in Hs; case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; simpl in * |- *;
  unfold buff_read_step in * |- *; auto.

  case_eq (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r))); intro Hb; auto.
      case_eq (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E pp L)) ((*rc*) (hb E (p2X E pp L))) e r))); intro Hbpp; rewrite Hbpp in Hs; auto.
      generalize (bemp_axf (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E pp L)) ((*rc*) (hb E (p2X E pp L))) e r) Hbpp); intros [e [Heb Hlc]].
      generalize (bemp_axt (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r) Hb); intro Hnex.
      assert (exists e, ran (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) e /\ rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r) as Hc.
        exists e; split; auto.
          destruct Hlc as [e' [Hee' He'r]]; exists e'; split; auto.
          apply A.wit_incl with (p2X E pp L); auto. 
      contradiction.
      case_eq (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E pp L)) ((*rc*) (hb E (p2X E pp L))) e r))); intro Hbpp; rewrite Hbpp in Hs; auto.
      generalize (bemp_axf (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r) Hb); intros [e [Heb Hlc]].
      generalize (bemp_axt (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E pp L)) ((*rc*) (hb E (p2X E pp L))) e r) Hbpp); intro Hnex.
      assert (exists e, ran (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) e /\ rel_seq (A.prop E (p2X E pp L)) ((*rc*) (hb E (p2X E pp L))) e r) as Hc.
        exists e; split; auto.
          destruct Hlc as [e' [Hee' He'r]]; exists e'; split; auto.
          apply A.wit_incl with (p2X E p L); auto. 
      contradiction.

  intros w Hde; rewrite Hde in Hs; simpl in * |- *;
  unfold buff_write_step in * |- *; auto.
case_eq (is_emp
         (Intersection _ (B s1)
            (fun e => (A.prop E (p2X E pp L)) w e))); intros Hbqp; auto;
    rewrite Hbqp in Hs. Focus 2.
      assert (is_emp
         (Intersection _ (B s1) 
            (fun e => (A.prop E (p2X E p L)) w e)) = false) as Hbq.
        case_eq (is_emp (Intersection _ (B s1) 
         (fun e => (A.prop E (p2X E p L)) w e))); intro Hb; auto.
        generalize (is_emp_axf (B s1) (fun e => (A.prop E (p2X E pp L)) w e) Hbqp);
          intros [e [Hbq Hrr]].
        generalize (is_emp_axt (B s1) (fun e : Event => (A.prop E (p2X E p L)) w e) Hb); intro Hn.
        assert (exists e : Event, (B s1) e /\ (A.prop E (p2X E p L)) w e) as Hc.
          exists e; split; auto.
            apply prop_incl_monot with pp; auto. 
        contradiction.

      rewrite Hbq; auto.
      assert (is_emp
         (Intersection _ (B s1) 
            (fun e => (A.prop E (p2X E p L)) w e)) = true) as Hbq.
        case_eq (is_emp (Intersection _ (B s1)
         (fun e => (A.prop E (p2X E p L)) w e))); intro Hb; auto.
        generalize (is_emp_axf (B s1) (fun e => (A.prop E (p2X E p L)) w e) Hb);
          intros [e [Hbq Hrr]].
        generalize (is_emp_axt (B s1) (fun e => (A.prop E (p2X E pp L)) w e) Hbqp); intro Hn.
        assert (exists e, ((B s1)) e /\ (A.prop E (p2X E pp L)) w e) as Hc.
          exists e; split; auto.
            apply prop_wit_incl with (p2X E p L); auto.
        contradiction.
      rewrite Hbq; auto.

  intros [w r] Hde; rewrite Hde in Hs; simpl in * |- *; auto.

  intros w Hde; rewrite Hde in Hs; simpl in * |- *; auto.
  unfold flush_write_step in * |- *.
    destruct (bin ((B s1)) w); auto.
  case_eq ( bemp
           (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ (A.prop E (p2X E pp L)) w1 w2) /\
               w1 = w) (fun e : Event => udr (Rcp s1) e))); intro Hb;
  rewrite Hb in Hs. Focus 2.

  assert (bemp
       (rrestrict
          (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
           w1 = w) (fun e : Event => udr (Rcp s1) e)) = false) as Hbf.
    case_eq (bemp
       (rrestrict
          (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
           w1 = w) (fun e : Event => udr (Rcp s1) e))); intro Hbp; auto.
    generalize (bemp_axf (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E pp L)) w1 w2) /\
           w1 = w) (fun e : Event => udr (Rcp s1) e) Hb); intros [e [Hipp Hrpp]].
    generalize (bemp_axt (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
           w1 = w) (fun e : Event => udr (Rcp s1) e) Hbp); intros Hn.
    assert (exists e : Event,
           ran
          (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\ 
           w1 = w) e /\ udr (Rcp s1) e) as Hy.
      exists e; split; auto.
      destruct Hipp as [e' [Hor Heq]]; exists e'; split; auto.
        inversion Hor as [|Hseq]; auto.
          right; apply prop_wit_incl with (p2X E pp L); auto.
    contradiction.

    rewrite Hbf; auto.

    assert (bemp
       (rrestrict
          (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
           w1 = w) (fun e : Event => udr (Rcp s1) e)) = true) as Hpbt.
      case_eq (bemp
       (rrestrict
          (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
           w1 = w) (fun e : Event => udr (Rcp s1) e))); intro Hbp; auto.
      generalize (bemp_axf (fun w1 w2 : Event =>
            (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\ 
            w1 = w) (fun e : Event => udr (Rcp s1) e) Hbp); intros [e [Heb Hercp]].
      generalize (bemp_axt (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E pp L)) w1 w2) /\
           w1 = w) (fun e : Event => udr (Rcp s1) e) Hb); intro Hn.
      assert (exists e : Event,
        ran
          (fun w1 w2 : Event =>
           (po_loc E w1 w2 \/ (A.prop E (p2X E pp L)) w1 w2) /\
           w1 = w) e /\ udr (Rcp s1) e) as Hy.
         exists e; split; auto.
         destruct Heb as [e' [Hor Heq]]; exists e'; split; auto.
         inversion Hor as [|Hseq]; auto.
           right; apply prop_wit_incl with (p2X E p L); auto.
       contradiction.
    rewrite Hpbt; auto.
Qed.

Lemma incl_and_last_is_pred :
  forall d p L l,
  Included Label (Union Label (dom p) (ran p)) L ->
  trans p -> acyclic p ->
  (forall l1 l2 : Label, l1 <> l2 -> L l1 -> L l2 -> p l1 l2 \/ p l2 l1) ->
  (forall d l, rel_incl d (pred p l) ->
     (forall x1 x2, x1 <> x2 -> (p x1 l) -> (p x2 l) ->
      d x1 x2 \/ d x2 x1)) -> 
  rel_incl d (pred p l) ->
  ~(exists l', tc p (Last.last d) l' /\ tc p l' l) \/ Last.last d = l ->
  d = pred p l.
Proof.
intros d p L l Hudrp Htp Hacp Htotp Htot Hi Hor; apply ext_rel; intros x y; split; intro Hxy.
  apply Hi; auto.
  destruct Hxy as [Hxy Hyl].
  inversion Hor as [Hn | Hl]; clear Hor.
    destruct (eqLabel_dec (Last.last d) y) as [Heq | Hneq].
      assert (d x y \/ d y x) as Hord.
        apply Htot with l; auto.
          intros Heqxy; rewrite Heqxy in Hxy.
            rewrite <- trans_tc with Label p in Hxy; auto; apply (Hacp y Hxy); auto.
            apply Htp with y; auto.
      inversion Hord as [|Hdyx]; clear Hord; auto.
        generalize (Hi y x Hdyx); intros [Hyx ?].
        assert (tc p x x) as Hc.
          apply trc_ind with y; apply trc_step; auto.
        generalize (Hacp x Hc); intro Ht; inversion Ht; auto.
      assert (p (Last.last d) y \/ p y (Last.last d)) as Hor.
        apply Htotp; auto.
          assert (Last.last d = Last.last d) as Ht.
            auto.
          apply Hudrp; generalize (Last.last_in_ran d (Last.last d) Ht); intros [e He];
          generalize (Hi e (Last.last d) He); intros [? ?]; right; exists e; auto.
          apply Hudrp; right; exists x; auto.
      inversion Hor as [Hldy | Hyld]; clear Hor.
        assert (exists l' : Label, tc p (Last.last d) l' /\ tc p l' l) as Hc.
          exists y; split; apply trc_step; auto.
        contradiction.
        assert (d x y \/ d y x) as Hord.
          apply Htot with l; auto.
            intros Heqxy; rewrite Heqxy in Hxy.
              rewrite <- trans_tc with Label p in Hxy; auto; apply (Hacp y Hxy); auto.
              apply Htp with y; auto.
        inversion Hord as [|Hdyx]; clear Hord; auto.
          generalize (Hi y x Hdyx); intros [Hyx ?].
          assert (tc p x x) as Hc.
            apply trc_ind with y; apply trc_step; auto.
          generalize (Hacp x Hc); intro Ht; inversion Ht; auto.
      assert (d x y \/ d y x) as Hord.
        apply Htot with l; auto.
          intros Heqxy; rewrite Heqxy in Hxy.
            rewrite <- trans_tc with Label p in Hxy; auto; apply (Hacp y Hxy); auto.
            apply Htp with y; auto.
      inversion Hord as [|Hdyx]; clear Hord; auto.
        generalize (Hi y x Hdyx); intros [Hyx ?].
          assert (tc p x x) as Hc.
            apply trc_ind with y; apply trc_step; auto.
          generalize (Hacp x Hc); intro Ht; inversion Ht; auto.
Qed.

Definition loc_of_label lb :=
  match lb with
  | d de | f de => loc (evt_of_devt de) end.

Lemma upd_buff_id :
  forall (B:Buffer) e,
  B dB e ->
  upd_buff B e = B.
Proof.
intros B e Hi; apply ext_rel; intros x y; split; intro Hxy.
  unfold upd_buff in Hxy; auto.
  case_eq (bin (udr B) e); intro Hib.
    rewrite Hib in Hxy; auto.
    assert (bin (udr B) e = true) as Hib'.
      apply In_bin; right; exists dB; auto.
    rewrite Hib in Hib'; inversion Hib'.

  unfold upd_buff; 
  destruct (bin (udr B) e); auto.
  left; auto.
Qed.

Lemma upd_wfb :
  forall E (B:Buffer) w, 
  (forall w1 w2, 
   events E w1 -> events E w2 ->
   w1 <> w2 ->
   ran B w1 ->
   ran B w2 ->
   loc w1 = loc w2 -> B w1 w2 \/ B w2 w1) ->
  (forall w1 w2, 
   events E w1 -> events E w2 ->
   w1 <> w2 ->
   ran (upd_buff B w) w1 ->
   ran (upd_buff B w) w2 ->
   loc w1 = loc w2 -> upd_buff B w w1 w2 \/ upd_buff B w w2 w1).
Proof.
intros E B' w Hwfb w1 w2 He1 He2 Hd H1 H2 Hl.

  unfold upd_buff in * |- *; case_eq (bin (udr B') w); intro Hib; 
  rewrite Hib in * |-*; auto.

    destruct H1 as [x1 H1]; destruct H2 as [x2 H2].
    inversion H1 as [Hb1 | Heq1]; clear H1; 
    inversion H2 as [Hb2 | Heq2]; clear H2.
      assert (ran B' w1) as Hr1.
        exists x1; auto.
      assert (ran B' w2) as Hr2.
        exists x2; auto.
      generalize (Hwfb w1 w2 He1 He2 Hd Hr1 Hr2 Hl); intro Hor; inversion Hor as [H12 | H21]; clear Hor; [left | right]; left; auto.
      destruct Heq2 as [? Heq2]; left; right; split; auto; right; subst; auto; split; auto; exists x1; auto.
      destruct Heq1 as [? Heq1]; right; right; split; auto; right; subst; auto; split; auto; exists x2; auto.
      destruct Heq1 as [? Heq1]; destruct Heq2 as [? Heq2]; rewrite <- Heq2 in Heq1; contradiction.   
Qed.
  
Lemma tc_updb :
  forall B w a x y,
  w <> dB ->
  trans B ->
  tc (rrestrict (upd_buff B w) (fun e => loc e = a)) x y ->
  tc (rrestrict B (fun e => loc e = a)) x y \/ ((x = dB \/ udr B x) /\ (y <> dB /\ ~(udr B y))).
Proof.
intros B w a x y HndB Htr Hxy.
induction Hxy as [x y [Hs ?] |]. 
  
  unfold upd_buff in Hs; case_eq (bin (udr B) w); 
    intro Hi; rewrite Hi in Hs.
    left; apply trc_step; split; auto.
    inversion Hs as [Hb | [[HdB | [Hib ?]] Heq]]; auto.
      left; apply trc_step; split; auto.
      right; split; auto.
        subst; split; auto.
          intro Hibw; generalize (In_bin (udr B) w Hibw); intro Ht;
          rewrite Ht in Hi; inversion Hi. 
      right; split; auto.
        right; right; auto. 
        subst; split; auto. 
          intro Hibw; generalize (In_bin (udr B) w Hibw); intro Ht;
          rewrite Ht in Hi; inversion Hi.

  inversion IHHxy1 as [Hxz | [Hx [? Hnz]]];
  inversion IHHxy2 as [Hzy | [Hz Hny]].

    left; apply trc_ind with z; auto.
    right; split; auto.
      rewrite trans_tc in Hxz; auto. 
        destruct Hxz as [? ?]; auto; right; left; exists z; auto.
        intros e1 e2 e3 [H12 [? ?]] [H23 [? ?]]; split; [|split]; auto.
          apply Htr with e2; auto.

    rewrite trans_tc in Hzy; auto.
      assert (udr B z) as Hc.
        destruct Hzy as [? ?]; left; exists y; auto.
      contradiction.
        intros e1 e2 e3 [H12 [? ?]] [H23 [? ?]]; split; [|split]; auto.
          apply Htr with e2; auto.      

    right; split; auto.
Qed.

Lemma acb_persistent :
  forall B w,
  w <> dB ->
  trans B ->
  acyclic (rrestrict B (fun e => loc e = loc w)) ->
  acyclic (rrestrict (upd_buff B w) (fun e => loc e = loc w)).
Proof.
intros B w HndB Htr Hac x Htc.
generalize (tc_updb B w (loc w) x x HndB Htr Htc); intro Hor.
inversion Hor as [Hc | [Hx [HndBx Hnx]]].

  apply Hac with x; auto.

  inversion Hx; contradiction.
Qed.

Lemma tc_updb' :
  forall B e w x y,
  loc e <> loc w ->
  tc (rrestrict (upd_buff B w) (fun w0 : Event => loc w0 = loc e)) x y ->
  tc (rrestrict B (fun w0 : Event => loc w0 = loc e)) x y.
Proof.
intros B e w x y Hl Hxy.

induction Hxy as [x y [Hs [Hlx Hly]] |].
  unfold upd_buff in Hs; destruct (bin (udr B) w).
    apply trc_step; split; auto.
    inversion Hs as [? | [Hor Hw]].
      apply trc_step; split; auto.
      unfold Ensembles.In in Hly; rewrite Hw in Hly; assert False as Ht.
        apply Hl; auto.
      inversion Ht.

  apply trc_ind with z; auto.
Qed.
    
Lemma updb_trans :
  forall E (B:Rln Event) w,
  wf_buff E B ->
  (forall w1 w2, B w1 w2 -> w1 <> dB -> loc w1 = loc w2) ->  
  trans B ->
  trans (upd_buff B w).
Proof.
intros E B w Hwfb Hrrl Htr; unfold upd_buff; case_eq (bin (udr B) w); [intros Hi | intros Hni]; 
intros e1 e2 e3 H12 H23.

  apply Htr with e2; auto.
  
  inversion H12 as [Hb12 | [Hor12 H2]]; inversion H23 as [Hb23 | [Hor23 H3]].
    left; apply Htr with e2; auto.
    inversion Hor23 as [HdB | [? Hl]].
      assert (ran B dB) as Hr.
        exists e1; rewrite <- HdB; auto.
      generalize (dB_not_ran B Hr); intro Ht; inversion Ht.
      right; split; auto.
        destruct (eqEv_dec e1 dB) as [Heq | Hneq].
        left; auto.
        right; split; auto.
          exists dB; assert (udr B e1) as Hudr.  
            left; exists e2; auto.
          generalize (udr_dB B e1); intros [d b]. 
          generalize (d Hudr); intros [? ?]; auto.
              rewrite <- Hl; apply Hrrl; auto.

      assert (bin (udr B) w = true) as Ht.
        apply In_bin; left; exists e3; subst; auto.
      rewrite Ht in Hni; inversion Hni.

    right; split; auto.
Qed.

Lemma wfb_upd :
  forall B E L w,
  wf_labels E L -> wf_rf_labels E L ->
  events E w -> 
  L (d (DW w)) ->
  wf_buff E B ->
  wf_buff E (upd_buff B w).
Proof.
intros B E L w Hwfl Hwfrfl Hew Hl [Hudr [Htot [Hac [Htrans Hrrl]]]]; split; [|split; [|split; [|split]]].

  intros ? [e [e' Hd] | e [e' Hr]] HndB.
  unfold upd_buff in Hd.
    destruct (bin (udr B) w).
      apply Hudr; auto; left; exists e'; auto.
      inversion Hd as [Hb | [[HdB | [Hb ?]] ?]].
        apply Hudr; auto; left; exists e'; auto.
        assert False as Ht.
          apply HndB; auto.
        inversion Ht.
        apply Hudr; auto; right; auto.

  unfold upd_buff in Hr.
    destruct (bin (udr B) w).
      intros; apply Hudr; auto; right; exists e'; auto.
      inversion Hr as [Hb | [[HdB | [Hb ?]] ?]].
        apply Hudr; auto; right; exists e'; auto.
          destruct Hwfl as [[Hd ?] ?]; apply Hd; subst; auto.
          destruct Hwfl as [[Hd ?] ?]; apply Hd; subst; auto.

  intros w1 w2 He1 He2 Hdiff Hr1 Hr2 Heql; apply upd_wfb with E; auto.
  intros e.
    destruct (eqLoc_dec (loc e) (loc w)) as [Heq | Hneq].
      rewrite Heq; apply acb_persistent; auto.

      destruct Hwfl as [[Hd ?] ?].
        intro Heqw; rewrite Heqw in Hew; generalize (dB_not_in_E E dB Hew); intro Hc. 
        assert False as Ht.
          apply Hc; auto.
        inversion Ht.      
 
    intros x Hx; generalize (tc_updb' B e w x x Hneq Hx); intro Hc.
      apply (Hac e x Hc).

  apply updb_trans with E; auto.
  split; auto; split; auto.

  intros w1 w2; unfold upd_buff; case_eq (bin (udr B) w); intros Hi.
    intros Hb; apply Hrrl; auto.
    intros [Hb | [Hor Hw]].
      apply Hrrl; auto.
        inversion Hor as [HdB | [? Heql]].
          intro HndB; assert False as Ht.
            apply HndB; auto.
          inversion Ht.
          subst; auto.
Qed.

Lemma po_fr :
  forall E X r w,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  reads E r -> writes E w ->
  po_iico E r w -> loc r = loc w ->
  fr E X r w.
Proof.
intros E X r w Hwf Hv Hr Hw Hpo Hl.
destruct_valid Hv.
generalize (Hrf_init r Hr); intros [wr [Hewr Hrf]].

assert (po_loc_llh E r w) as Hpio.
  split; [|split]; auto.
    intros [? [? [l [v Haw]]]];
    destruct Hw as [? [? [? Har]]].
    rewrite Haw in Har; inversion Har.

destruct (eqEv_dec w wr) as [Heq | Hneq].

assert (com' E X w r) as Hhb.
  rewrite Heq; left; left; left; left; auto.
generalize (Huni r w Hpio); intro; contradiction.

assert (ws X w wr \/ ws X wr w) as Hor.
  generalize (Hws_tot (loc w)); intro Hlin; destruct_lin Hlin.
  assert ((writes_to_same_loc_l (events E) (loc w)) w) as Hww.
    destruct Hw as [? [l [v Haw]]]; 
    split; auto; exists v; unfold loc; rewrite Haw; auto.
  assert ((writes_to_same_loc_l (events E) (loc w)) wr) as Hwwr.
    rewrite <- Hl; rewrite <- ABasic.rf_implies_same_loc2 with E X wr r; auto.
    split; auto.
    generalize (ABasic.dom_rf_is_write E X wr r Hrf_cands Hrf);
    intros [l [v Haw]]; exists v; unfold loc; rewrite Haw; auto.
      split; split; auto.
     
  generalize (Htot w wr Hneq Hww Hwwr); intros [[? ?]|[? ?]]; auto.

inversion Hor as [Hwwr | Hwrw].

  assert (com' E X w r) as Hhb.
    left; right; exists wr; split; auto.
  generalize (Huni r w Hpio); intro; contradiction.

  split; [|split]; auto. 
    destruct Hr; auto.
    destruct Hw; auto.
    exists wr; split; auto.
Qed.

Lemma contrad_ppo_b :
  forall E X n s0 s1 e phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) -> 
  wf_devts E ->
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  events E (evt_of_devt (DW e)) ->
  labels_of_es E X (d (DW e)) ->
  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->
  (exists dr, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (d (DW e))) /\
    (~(exists l' : Label,
       tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
       tc (OEL.LE (tc (X2p E X))) l' (d (DW e))) \/ Last.last dr = d (DW e)) /\
     machine E dr (labels_of_es E X) (d (DW e)) n phi (Some s0) (Some s1)) ->
  is_emp (Intersection _ (B s1) (fun e' => (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) (evt_of_devt (DW e)) e')) = false ->
  False.
Proof.
intros E X n s0 s1 e' phi Hwf Hv Hwfl Hwfrfl Hwfd Hwfb Hwfq Hede' Hlde' Hfifo Hem Hppo.
  generalize Hwfl; intros Hwfl'.
  generalize (is_emp_axf (B s1) (fun e => (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) (evt_of_devt (DW e')) e) Hppo);
  clear Hppo; intros [e [Hi Hppo]].

        assert (Included _ (labels_of_es E X) (labels_of_es E X)) as Htl.
          intros l Hl; auto.
        assert (partial_order (tc (X2p E X)) (labels_of_es E X)) as Hpl.
          apply tc_X2p_partial_order; auto.
        generalize (OEL.OE (labels_of_es E X) (labels_of_es E X) (tc (X2p E X)) Htl Hpl);
          clear Htl; intros [Hil Hl].
        assert (trans (OEL.LE (tc (X2p E X)))) as Httc.
          destruct_lin Hl; intros x y z Hxy Hyz; apply Htrans with y; auto.

      (*destruct Hi as [x Hb].
        assert (udr (B s1) e) as Hudr.
          right; exists x; auto.*)
        assert (tc (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) (evt_of_devt (DW e')) e) as Htc.
          apply trc_step; auto.
        assert (events E e) as Hee.
            generalize (ran_prop_W E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)) (evt_of_devt (DW e')) e Htc); intros [? ?]; auto.

  generalize (in_buff_implies_before E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (d (DW e')) n s0 s1 e phi Httc Hee Hi Hem); 
  intro Hee'.

    assert (acyclic (OEL.LE (tc (X2p E X)))) as Hac'.   
      unfold acyclic; auto.
      intros x' Hx'. 
        rewrite trans_tc in Hx'.
        destruct_lin Hl; apply (Hac x' Hx'); auto.
          apply oel_trans with (labels_of_es E X).
            apply tc_X2p_partial_order; auto.

    assert (tc (OEL.LE (tc (X2p E X))) (d (DW e)) (d (DW e))) as Hc.
      apply trc_ind with (d (DW e')); auto; apply trc_step; auto.
        apply Hfifo; apply Hil; apply trc_step; apply X2p_prop; auto.
        simpl; rewrite <- p2X_X2p with E X; auto; apply trc_step; auto.
        left; exists e'; split; auto.
          destruct Hwfl as [[Hdw ?] ?]; apply Hdw.
          destruct_lin Hl; apply Hdr; auto; right; exists (d (DW e)); auto.
        left; exists e; split; auto.

    rewrite trans_tc in Hc; auto.
    destruct_lin Hl; apply (Hac (d (DW e))); auto.
Qed.

Lemma uniws_contrad' :
  forall E X n s0 s1 w1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_devts E ->
  writes E w1 ->
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  ((forall w2 w3 : Event,
    OEL.LE (tc (X2p E X)) (f (DW w2)) (f (DW w3)) ->
    OEL.LE (tc (X2p E X)) (d (DW w2)) (d (DW w3)))) ->
  (exists dr, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (d (DW w1))) /\ 
    (~(exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (d (DW w1))) \/ Last.last dr = d (DW w1)) /\
     machine E dr (labels_of_es E X) (d (DW w1)) n phi (Some s0) (Some s1)) ->
  is_emp (Intersection _ (B s1) (fun e => po_iico E w1 e /\ loc w1 = loc e)) = true.
Proof.
intros E X n s0 s1 w1 phi Hwf Hv Hwfl Hwfrfl Hwfd Hw1 Hwfb Hwfrs Hfifo Hm.
case_eq (is_emp (Intersection _ (B s1) (fun e => po_iico E w1 e /\ loc w1 = loc e))); intro Hb; auto.
generalize (is_emp_axf (B s1) (fun e => po_iico E w1 e /\ loc w1 = loc e) Hb); intros [e [Hbe [Hpo Hl]]].
apply sym_eq in Hl.
assert (coherence_well_formed (events E) (co X)) as Hwswf.
  destruct_valid Hv; auto.
  split; auto.
assert (events E e) as He.
  apply ABasic.po_iico_range_in_events with w1; auto.
assert (e <> dB) as HndB.
  apply dB_not_in_E with E; auto.

generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudrp.

assert ((B s1) e) as Hudr.
  (*right;*) auto.

generalize (in_buff_implies_before E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (d (DW w1)) n s0 s1 e phi Htp He Hudr Hm);
intros He1.
assert (tc (OEL.LE (tc (X2p E X))) (d (DW w1)) (d (DW e))) as H1e.
  apply trc_step; apply Hfifo; apply Hi; apply trc_step; apply X2p_ws; auto.

  destruct_valid Hv; destruct_lin (Hws_tot (loc w1)).
  assert (w1 <> e) as Hdiff.
    intro Heq; rewrite Heq in Hpo.
    apply (ABasic.po_ac Hwf Hpo).
  assert ((writes_to_same_loc_l (events E) (loc w1)) w1) as Hisw1.
    destruct Hw1 as [? [? [v Haw1]]]; split; auto.
    exists v; unfold loc; rewrite Haw1; auto.
  assert ((writes_to_same_loc_l (events E) (loc w1)) e) as Hiswe.
    generalize (Hwfb e Hudr); intros [? [l [v Hawe]]];
    split; auto; exists v; rewrite <- Hl; unfold loc; rewrite Hawe; auto.
  generalize (Htot w1 e Hdiff Hisw1 Hiswe); intros [[Hco1e ?] | [Hcoe1 ?]]; auto.
  assert False as Ht.
    unfold AWmm.uniproc in Huni; unfold AWmm.com_vs_po in Huni.
    apply (Huni w1 e).
      split; [|split]; auto.
      intros [? [? [? [? Hre]]]].
      generalize (ABasic.dom_ws_is_write E X e w1 Hwswf Hcoe1);
      intros [? [? Hwe]].
      rewrite Hwe in Hre; inversion Hre; auto.
      left; left; right; auto.
  inversion Ht.

  apply if_ldw_then_lfw with E; auto.
    apply Hudrp; right; exists (d (DW e)); auto.
  apply if_ldw_then_lfw with E; auto.
    apply Hudrp; left; exists (d (DW w1)); auto.
assert (tc (OEL.LE (tc (X2p E X))) (d (DW w1)) (d (DW w1))) as Hc.
  apply trc_ind with (d (DW e)); auto; apply trc_step; auto.
generalize (Hacp (d (DW w1)) Hc); intro Ht; inversion Ht.
Qed. (*should be ok by Hpo/anyway maybe it's ok to have fifo hyp in this drn*)

Lemma contrad_wr :
  forall E X n s0 s1 w1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_devts E ->
  writes E w1 ->
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
(*  ((forall w2 w3 : Event,
    OEL.LE (tc (X2p E X)) (f (DW w2)) (f (DW w3)) ->
    OEL.LE (tc (X2p E X)) (d (DW w2)) (d (DW w3)))) ->*)
  (exists dr, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (d (DW w1))) /\ 
    (~(exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (d (DW w1))) \/ Last.last dr = d (DW w1)) /\
     machine E dr (labels_of_es E X) (d (DW w1)) n phi (Some s0) (Some s1)) ->
  is_emp (Intersection Event (Rs s1)
               (fun r' : Event => (A.fences E) w1 r')) = true.
Proof.
intros E X n s0 s1 w1 phi Hwf Hv Hwfl Hwfrfl Hwfd Hw1 Hwfb Hwfrs (*Hfifo*) Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudr.

case_eq (is_emp (Intersection Event (Rs s1)
               (fun r' : Event => (A.fences E) w1 r'))); intro Hemp; auto.
generalize (is_emp_axf (Rs s1) (fun r' : Event => (A.fences E) w1 r') Hemp);
intros [e [Hrs H1e]].
assert (exists we, labels_of_es E X (f (DR (we,e)))) as Hex.
  assert (reads E e) as Hre.
    apply Hwfrs; auto.
  destruct Hwfrfl as [Hlr ?]; generalize (Hlr e Hre);
  intros [we [? Hlwe]]; exists we; auto.
destruct Hex as [we Hle].
assert (labels_of_es E X (f (DW w1))) as Hl1.
  destruct Hwfl as [? [? [Hfw ?]]]; apply Hfw; auto.
assert (tc (OEL.LE (tc (X2p E X))) (d (DW w1)) (d (DR (we,e)))) as Hp1e.
  apply trc_step; apply Hi; apply trc_step; apply X2p_fencewr; auto.

assert (tc (OEL.LE (tc (X2p E X))) (d (DR (we,e))) (d (DW w1))) as Hpe1.
  apply in_rs_implies_d_before with E (labels_of_es E X) n s0 s1 e phi; auto.
    rewrite trans_tc; auto.
    intros x y z Hxy Hyz; apply trc_ind with y; auto.
    generalize (Hwfrs e Hrs); intros [? ?]; auto.
    destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.
    rewrite trans_tc; auto.

assert (tc (OEL.LE (tc (X2p E X))) (d (DW w1)) (d (DW w1))) as Hc.
  apply trc_ind with (d (DR (we,e))); auto.
assert False as Ht.
  apply (Hacp (d (DW w1))); auto.
inversion Ht.
Qed.

Lemma dwrites_dont_block_ex :
  forall E X n s0 s1 w1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  writes E w1 -> 
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  (exists r, trans r /\ rel_incl r (pred (OEL.LE (tc (X2p E X))) (d (DW w1))) /\ 
    (~(exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (Last.last r) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (d (DW w1))) \/ Last.last r = d (DW w1)) /\
     machine E r (labels_of_es E X) (d (DW w1)) n phi (Some s0) (Some s1)) ->
  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->
  ~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (d (DW w1)) phi = None).
Proof.
intros E X n s0 s1 w1 phi Hwf Hv Hwfd Hwfl Hwfrfl Hew1 Hwfb Hwfq Hed' Hfifo Hs; simpl in Hs;
unfold buff_write_step in Hs.
assert (exists d0, rel_incl d0 (pred (OEL.LE (tc (X2p E X))) (d (DW w1))) /\
         (~(exists l' : Label,
         tc (OEL.LE (tc (X2p E X))) (Last.last d0) l' /\
         tc (OEL.LE (tc (X2p E X))) l' (d (DW w1))) \/ Last.last d0 = d (DW w1)) /\
        machine E d0 (labels_of_es E X) (d (DW w1)) n phi (Some s0) (Some s1)) as Hed.
  destruct Hed' as [r [? [? [? ?]]]]; exists r; split; auto.

case_eq (is_emp
           (Intersection Event (Rs s1)
              (fun r' : Event => (A.fences E) w1 r')));
  intro Hci0_wr; rewrite Hci0_wr in Hs.

case_eq (is_emp (Intersection _ (B s1) (fun e : Event => po_iico E w1 e /\ loc w1 = loc e)));
  intro Hunip; rewrite Hunip in Hs.

case_eq (is_emp (Intersection _ (B s1) (fun e => (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) w1 e)));
  intro Hlcw; rewrite Hlcw in Hs.

    inversion Hs.

  apply contrad_ppo_b with E X n s0 s1 w1 phi; auto.
    destruct Hew1 as [? ?]; auto. 
    destruct Hwfl as [? [? [Hw Hldf]]]; apply Hldf; apply Hw; auto.

  rewrite uniws_contrad' with E X n s0 s1 w1 phi in Hunip; auto; inversion Hunip.

  rewrite contrad_wr with E X n s0 s1 w1 phi in Hci0_wr; auto; inversion Hci0_wr.
Qed.

Lemma dwrites_dont_block :
  forall E X n s0 s1 w1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  writes E w1 -> 
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  machine E (pred (OEL.LE (tc (X2p E X))) (d (DW w1))) (labels_of_es E X) (d (DW w1)) n phi (Some s0) (Some s1) ->
  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->
  ~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (d (DW w1)) phi = None).
Proof.
intros E X n s0 s1 w1 phi Hwf Hv Hwfd Hwfl Hwfrfl Hew1 Hwfm Hwfb Hwfq Hfifo.
apply dwrites_dont_block_ex with n s0; auto.
  exists (pred (OEL.LE (tc (X2p E X))) (d (DW w1))); split; [|split; [|split]]; auto.
    apply td_tpred; auto. 
      apply oel_trans with (labels_of_es E X); auto.
      apply tc_X2p_partial_order; auto; intros x y Hxy; auto. 
    intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.
Qed.

Lemma rcp_ws' :
  forall E X n s0 s1 lst w w' phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  wf_buff E (Rcp s1) -> wf_rs E (Rs s1) ->
  (exists r, trans r /\ rel_incl r ((pred (OEL.LE (tc (X2p E X))) lst)) /\ 
    (~(exists l' : Label,
       tc (OEL.LE (tc (X2p E X))) (Last.last r) l' /\
       tc (OEL.LE (tc (X2p E X))) l' lst) \/ Last.last r = lst) /\
     machine E r (labels_of_es E X) lst n phi (Some s0) (Some s1)) ->
  Rcp s1 w w' -> loc w = loc w' -> w <> dB ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  ws X w w'.
Proof. 
intros E X n s0 s1 lst w w' phi Hwf Hv Hwfd Hwfl Hwfrfl Hwfb Hwfq Hed' Hww' Heql HndB (*Hfifo*).

generalize Hv; intro Hv'; destruct_valid Hv'.
generalize (Hws_tot (loc w)); intro Hl; destruct_lin Hl.
 clear Hws_tot Hws_cands Hrf_init Hrf_cands Hrf_uni Hdr Hac Htrans.
  assert (w <> w') as Hd.
    intro Heq; rewrite Heq in Hww'.
    assert (tc (rrestrict (Rcp s1) (fun e => loc e = loc w')) w' w') as Hc.
      apply trc_step; split; auto.
        split; unfold Ensembles.In; auto.
    destruct Hwfb as [? [Ht [Hac ?]]]; apply (Hac w' w' Hc). 

  assert ((writes_to_same_loc_l (events E) (loc w)) w) as Hw.
    assert (udr (Rcp s1) w) as Hbw.
      left; exists w'; auto.
    destruct Hwfb as [Hudrb [? ?]]; generalize (Hudrb w Hbw); intros [? [? [v Haw]]]; auto.
    split; auto; exists v; auto; unfold loc; rewrite Haw; auto.
  assert ((writes_to_same_loc_l (events E) (loc w)) w') as Hw'.
    rewrite Heql.
    assert (udr (Rcp s1) w') as Hbw'.
      right; exists w; auto.
    destruct Hwfb as [Hudrb [? ?]]; generalize (Hudrb w' Hbw'); intros [? [? [v Haw']]]; auto.
    intro Heq; rewrite Heq in Hww'; assert (ran (Rcp s1) dB) as Hr.
      exists w; auto.
    apply (dB_not_ran (Rcp s1) Hr); auto.
    split; auto; exists v; auto; unfold loc; rewrite Haw'; auto.
  generalize (Htot w w' Hd Hw Hw'); intro Hor; 
    inversion Hor as [Hws|Hws]; clear Hor; destruct Hws as [Hws ?]; auto.
  generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.

  assert (OEL.LE (tc (X2p E X)) (f (DW w')) (f (DW w))) as Hp.    
    destruct Hwfl as [? [? [Hwl Hlfd]]].
    generalize (oel_incl (X2p E X) (labels_of_es E X)Hpart); intro Hi;
    apply Hi; apply trc_step; apply X2p_ws; auto. 
    apply Hwl; auto. 
      destruct Hw' as [? [v Haw]]; auto;
      split; auto; exists (loc w); exists v; auto. 
    apply Hwl; auto.
      destruct Hw as [? [v Haw]]; auto;
      split; auto; exists (loc w); exists v; auto. 
    clear Htot H.

  assert (linear_strict_order (OEL.LE (tc (X2p E X))) (labels_of_es E X)) as Hlin.
    assert (Included _ (labels_of_es E X) (labels_of_es E X)) as Hi.  
      intros x Hx; auto.
    generalize (OEL.OE (labels_of_es E X) (labels_of_es E X) (tc (X2p E X)) Hi Hpart); intros [? ?]; auto.
  assert (loc w' = loc w) as Heqloc.
    apply sym_eq; auto. 
  assert (Rcp s1 dB w') as Hiw'.
    assert (udr (Rcp s1) w') as Hudr.
      right; exists w; auto.
    generalize (udr_dB (Rcp s1) w'); intros [dir bak]; generalize (dir Hudr); intros [? ?]; auto.
  assert (Rcp s1 dB w) as Hiw.
    assert (udr (Rcp s1) w) as Hudr.
      left; exists w'; auto.
    generalize (udr_dB (Rcp s1) w); intros [dir bak]; generalize (dir Hudr); intros [? ?]; auto.
  assert (forall w r,
    labels_of_es E X (f (DR (w,r))) -> OEL.LE (tc (X2p E X)) (d (DR (w,r))) (f (DR (w,r)))) as Hdf.
    intros w0 r0 Hde; apply oel_df; auto.
  assert (labels_of_es E X (f (DW w'))) as Hlfw'.
    left; exists w'; split; auto.
    destruct Hwfb as [Hbw ?]; apply Hbw; auto. 
    right; exists dB; auto. 
    intro Heq; assert (ran (Rcp s1) dB) as Hr. 
      exists dB; subst; auto. 
    apply (dB_not_ran (Rcp s1) Hr). 
  generalize (p_rcp E (OEL.LE (tc (X2p E X))) (labels_of_es E X) lst n s0 s1 w' w phi Hwf Hlin Hwfl Hed' Hwfb Heqloc Hiw' Hiw Hp Hlfw');
  intros Hbw'w; auto. 

  destruct Hwfb as [? [? [Hacb ?]]].
  assert (tc (rrestrict (Rcp s1) (fun w0 : Event => loc w0 = loc w)) w w) as Hcy.
    apply trc_ind with w'; apply trc_step; split; unfold Ensembles.In; auto.
  generalize (Hacb w w Hcy); intro Ht; inversion Ht.
Qed.   

Hypothesis phi_tot :
  forall E phi w1 w2, 
  writes E w1 -> writes E w2 -> w1 <> w2 ->
  phi w1 w2 \/ phi w2 w1.

Lemma uniwsrf_contrad :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X -> 
  wf_devts E ->
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DW w1)) ->
  labels_of_es E X (f (DR (w1,r1))) ->
  rf X w1 r1 -> (waft E (B s1) r1) <> dB ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  po_iico E w1 r1 \/ bin (fun w => phi w (waft E (B s1) r1) /\ loc r1 = loc w) w1 = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfb Hwfq Hwfl Hwfrfl Hlfw Hlfwr Hrf Hndb Hm (*Hfifo*).
case_eq (bin (fun w => (phi w (waft E (B s1) r1)) /\ loc r1 = loc w) w1); auto.

assert (loc r1 = loc w1) as Heql.
  assert (rfmaps_well_formed E (events E) (rf X)) as Hwfrf.
    destruct_valid Hv; split; auto.
    apply sym_eq; apply ABasic.rf_implies_same_loc2 with E X; auto. split; auto.
      destruct_valid Hv; split; auto. 

intro Hf; generalize (nbin_nIn (fun w => (phi w (waft E (B s1) r1)) /\ loc r1 = loc w) w1 Hf); clear Hf; intro Hf.
generalize (in_order_implies_mem_or_buff_state E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfl Hlfw Hlfwr Hrf Hm); 
intros [Hpo | Hib]; auto; right.

generalize (EPick.pick_in (fun w => (B s1) w /\ loc r1 = loc w /\
                                    po_iico E r1 w /\
                                    ~ (exists w', loc r1 = loc w' /\ po_iico E r1 w' /\ po_iico E w' w)));
fold (waft E (B s1) r1); intros [Hr [Hl [Hpo Hn]]].

destruct (eqEv_dec w1 (waft E (B s1) r1)) as [Heq | Hneq].

  rewrite <- Heq in Hpo.
  assert (po_loc_llh E r1 w1) as Hpio.
    split; [|split]; auto.
      intros [? [? [? [? Har]]]].
      destruct_valid Hv; generalize (ABasic.dom_rf_is_write E X w1 r1 Hrf_cands Hrf);
      intros [? [? Haw]]; rewrite Haw in Har; inversion Har.
  assert (com' E X w1 r1) as Hhb.
    left; left; left; left; auto. 
  destruct_valid Hv; generalize (Huni r1 w1 Hpio); intro Ht; contradiction.
  assert (events E w1) as He1.
    apply ABasic.dom_rf_in_events with X r1; auto. 
    destruct_valid Hv; split; auto. 
  assert (events E (waft E (B s1) r1)) as Heaft.
    apply ABasic.po_iico_range_in_events with r1; auto. 

    assert (phi w1 (waft E (B s1) r1) \/ phi (waft E (B s1) r1) w1) as Hor.
      apply phi_tot with E; auto.

    inversion Hor as [H1aft | Haft1].
      assert False as Ht.
        apply Hf; split; auto.
      inversion Ht.

    generalize (phi_rcp E (OEL.LE (tc (X2p E X))) (labels_of_es E X) s0 phi (waft E (B s1) r1) w1 Haft1);
    intros [m [lst [s [Hwfrcp' [Hwfrs' [Hex Hrcp]]]]]].

    assert (ws X (waft E (B s1) r1) w1) as Ha1.
      apply rcp_ws' with E m s0 s lst phi; auto. 
      rewrite <- Heql; auto.

  assert (po_loc_llh E r1 (waft E (B s1) r1)) as Hpio.
    split; [|split]; auto.

        generalize (Hwfb (waft E (B s1) r1) Hr); auto.
        intros [? [? [? Haw]]]; intros [? [? [? [? Har]]]].
        rewrite Har in Haw; inversion Haw.

generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_ac (X2p E X) (labels_of_es E X) Hpart); intro Hac.

assert (exists r, trans r /\ rel_incl r (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) /\ 
           (~(exists l' : Label,
            tc (OEL.LE (tc (X2p E X))) (Last.last r) l' /\
            tc (OEL.LE (tc (X2p E X))) l' (f (DR (w1, r1)))) \/ Last.last r = f (DR (w1,r1))) /\
          machine E r (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1)) as Hed.
  exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))); split; [|split; [|split]]; auto.
    apply td_tpred; auto. 
    intros x y Hxy; auto. 
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto. 

  assert (com' E X (waft E (B s1) r1) r1) as Hhb.
    left; right; exists w1; split; auto.

  destruct_valid Hv; generalize (Huni r1 (waft E (B s1) r1) Hpio); intro Ht; contradiction.
Qed.

Lemma uwsrfc :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X -> 
  wf_devts E ->
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DW w1)) ->
  labels_of_es E X (f (DR (w1,r1))) ->
  rf X w1 r1 -> waft E (B s1) r1 <> dB ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  bin (fun e : Event => phi e (waft E (B s1) r1) /\ loc r1 = loc e \/
          po_loc E e r1 /\ e = w1) w1 = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfb Hwfq Hwfl Hwfrfl Hlfw Hlfwr Hrf Hndb Hm (*Hfifo*).
case_eq (bin (fun e : Event => phi e (waft E (B s1) r1) /\ loc r1 = loc e \/
          po_loc E e r1 /\ e = w1) w1); intro Hu; auto.
generalize (nbin_nIn (fun e : Event => phi e (waft E (B s1) r1) /\ loc r1 = loc e \/
          po_loc E e r1 /\ e = w1) w1 Hu); intro Hn.
assert False as Ht.
  apply Hn.
  generalize (uniwsrf_contrad E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfb Hwfq Hwfl Hwfrfl Hlfw Hlfwr Hrf Hndb Hm (*Hfifo*));
  intros [Hpo | Hb]; auto.
    right; split; auto.
      split; auto.
      apply ABasic.rf_implies_same_loc2 with E X; auto.
      destruct_valid Hv; split; split; auto.
    left; generalize (bin_In (fun w : Event => phi w (waft E (B s1) r1) /\ loc r1 = loc w) w1 Hb); auto.
inversion Ht.
Qed.

Lemma unifr_contrad :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X -> 
  wf_devts E ->
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DW w1)) ->
  labels_of_es E X (f (DR (w1,r1))) ->
  rf X w1 r1 ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  (*po_iico E w1 r1 \/*) bin (fun w => (w = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) w) /\ loc r1 = loc w) w1 = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfb Hwfq Hwfl Hwfrfl Hlfw Hlfwr Hrf Hm (*Hfifo*).
case_eq (bin (fun w => (w = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) w) /\ loc r1 = loc w) w1); auto.
assert (loc r1 = loc w1) as Heql.
  assert (rfmaps_well_formed E (events E) (rf X)) as Hwfrf.
    destruct_valid Hv; split; auto.
    apply sym_eq; apply ABasic.rf_implies_same_loc2 with E X; auto. split; auto.
      destruct_valid Hv; split; auto. 

intro Hf; generalize (nbin_nIn (fun w => (w = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) w) /\ loc r1 = loc w) w1 Hf); clear Hf; intro Hf.
(*  generalize (in_order_implies_mem_or_buff_state E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfl Hlfw Hlfwr Hrf Hm); 
    intros [Hpo | Hib]; auto. *)

generalize (EPick.pick_in (fun w => (B s1) w /\ loc r1 = loc w /\ po_iico E w r1 /\
   ~ (exists w' : Event, loc r1 = loc w' /\ po_iico E w w' /\ po_iico E w' r1)));
fold (wbef E (B s1) r1); intros [Hr [Hl [Hpo Hn]]].

destruct (eqEv_dec w1 (wbef E (B s1) r1)) as [Heq | Hneq].

  assert ((w1 = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) w1) /\ loc r1 = loc w1) as Hc.
    split; auto. 
  contradiction.
  assert (events E w1) as He1.
    apply ABasic.dom_rf_in_events with X r1; auto.
    destruct_valid Hv; split; auto. 
  assert (events E (wbef E (B s1) r1)) as Hebef.
    apply ABasic.po_iico_domain_in_events with r1; auto.
  (*rewrite Heql in Hl; generalize Hwfb; intros [? [Htb Hacb]];
  generalize (Htb w1 (wbef E (B s1) r1) He1 Hebef Hneq Hib Hr Hl); intro Hor; inversion Hor as [H1aft | Haft1]; clear Hor.*)

    generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
    generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
    generalize (oel_ac (X2p E X) (labels_of_es E X) Hpart); intro Hac.

 assert (w1 <> dB) as HndB.
   intro Heq; assert (events E dB) as He.
     rewrite <- Heq; apply ABasic.dom_rf_in_events with X r1; auto.
       destruct_valid Hv; split; auto. 
     apply (dB_not_in_E E dB He); auto.

assert (exists r : Rln Label,
    trans r /\
    rel_incl r (pred (OEL.LE (tc (X2p E X))) (f (DR (w1, r1)))) /\
    (~
     (exists l' : Label,
        tc (OEL.LE (tc (X2p E X))) (Last.last r) l' /\
        tc (OEL.LE (tc (X2p E X))) l' (f (DR (w1, r1)))) \/
     Last.last r = f (DR (w1, r1))) /\
    machine E r (labels_of_es E X) (f (DR (w1, r1))) n phi (Some s0) (Some s1)) as Hed.
  exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w1, r1)))); split; [|split; [|split]]; auto.
    apply td_tpred; auto.
    intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto. 

(* generalize (b_ws' E X n s0 s1 (f (DR (w1,r1))) w1 (wbef E (B s1) r1) Hwf Hv Hwfd Hwfl Hwfrfl (*Hwfm*) Hwfb Hwfq Hed H1aft Hl HndB (*Hfifo*)); intros Hws.*)
    assert (rfmaps_well_formed E (events E) (rf X)) as Hwfrf.
      destruct_valid Hv; split; auto.

    assert (phi (wbef E (B s1) r1) w1 \/ phi w1 (wbef E (B s1) r1)) as Hor.
      apply phi_tot with E; auto.
        split; auto.
        apply ABasic.dom_rf_is_write with E X r1; auto.
          destruct_valid Hv; auto.

    inversion Hor as [Hbef1 | H1bef].
      assert False as Ht.
        apply Hf; split; auto.
      inversion Ht.

    generalize (phi_rcp E (OEL.LE (tc (X2p E X))) (labels_of_es E X) s0 phi w1 (wbef E (B s1) r1) H1bef);
    intros [m [lst [s [Hwfrcp' [Hwfrs' [Hex Hrcp]]]]]].

  assert (co X w1 (wbef E (B s1) r1)) as Hws.
    apply rcp_ws' with E m s0 s lst phi; auto.
    rewrite <- Heql; auto.

  assert (fr E X r1 (wbef E (B s1) r1)) as Hfr.
    split; [|split]; auto.
      apply ABasic.ran_rf_in_events with X w1; auto. 

      exists w1; split; auto.

  destruct_valid Hv.

  assert (po_loc_llh E (wbef E (B s1) r1) r1) as Hpio.
    split; [|split]; auto.

      intros [[? [? [? Hrw]] ?]].
      assert (write_serialization_well_formed (events E) (ws X)) as Hwswf.
        split; auto.
      generalize (ABasic.ran_ws_is_write E X w1 (wbef E (B s1) r1) Hwswf Hws); intros [? [? Hww]].
      rewrite Hrw in Hww; inversion Hww.

  assert ((com' E X) r1 (wbef E (B s1) r1)) as Hhb.
    left; left; left; right; auto.

  generalize (Huni (wbef E (B s1) r1) r1 Hpio); intro Ht; contradiction.
Qed.

Lemma ufrc :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X -> 
  wf_devts E -> wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DW w1)) ->
  labels_of_es E X (f (DR (w1,r1))) ->
  rf X w1 r1 ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  bin (fun e => (e = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) e) /\
          loc r1 = loc e (*\/
          po_loc E e r1 /\
          ~(exists e' : Event,
             writes E e' /\
             loc e' = loc r1 /\ po_loc E e e' /\ po_loc E e' r1) /\ e = w1*)) w1 = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfb Hwfq Hwfl Hwfrfl Hlfw Hlfwr Hrf Hm (*Hfifo*).
case_eq (bin (fun e => (e = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) e) /\
          loc r1 = loc e) w1); intro Hu; auto.
assert False as Ht.
  generalize (nbin_nIn (fun e => (e = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) e) /\
          loc r1 = loc e (*\/
          po_loc E e r1 /\
          ~(exists e' : Event,
             writes E e' /\
             loc e' = loc r1 /\ po_loc E e e' /\ po_loc E e' r1) /\ e = w1*)) w1 Hu); intro Hn.
  apply Hn; generalize (unifr_contrad E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfb Hwfq Hwfl Hwfrfl Hlfw Hlfwr Hrf Hm (*Hfifo*));
  intros Hi. 
  generalize (bin_In (fun w : Event =>
        (w = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) w) /\
        loc r1 = loc w) w1 Hi); auto.
  inversion Ht.
Qed.
(*   [Hpo | Hb].
    right; split; [|split]; auto.
      split; auto. 
        apply ABasic.rf_implies_same_loc2 with E X; auto.
        destruct_valid Hv; split; split; auto.
      intros [e' [Hwe' [Hle' [Hw1e' He'r1]]]].
      destruct_valid Hv; unfold AWmm.uniproc in Huni; unfold AWmm.com_vs_po in Huni.
      apply (Huni e' r1).
        split; [|split]; auto.
        destruct He'r1; auto.
        intros [[? [? [? Hre']]] ?]; destruct Hwe' as [? [? [? Hwe']]];
        rewrite Hre' in Hwe'; inversion Hwe'.
        left; left; left; right; split; [|split]; auto. 
          apply ABasic.po_iico_range_in_events with w1; auto.
          destruct Hwe'; auto.
          exists w1; split; auto.
          assert (w1 <> e') as Hdw.
            intro Heq; rewrite Heq in Hw1e'; destruct Hw1e' as [? Hc].
            generalize Hc; apply ABasic.po_ac; auto.
          assert ((writes_to_same_loc_l (events E) (loc w1)) w1) as Hw1.
            split; auto.
              apply ABasic.po_iico_domain_in_events with r1; auto.
              generalize (ABasic.dom_rf_is_write E X w1 r1 Hrf_cands Hrf);
              intros [l [v Hw1]]; exists v; unfold loc; rewrite Hw1; auto.

          assert ((writes_to_same_loc_l (events E) (loc w1)) e') as Hw'.
            destruct Hwe' as [Hee' [l [v Hae']]]; split; auto.
            exists v; rewrite ABasic.rf_implies_same_loc2 with E X w1 r1; auto.
            rewrite <- Hle'; unfold loc; rewrite Hae'; auto.
            split; split; auto.

          assert (co X w1 e' \/ co X e' w1) as Hor.
            generalize (Hws_tot (loc w1)); intro Hcol.
            destruct_lin Hcol; generalize (Htot w1 e' Hdw Hw1 Hw'); 
            intros [[? ?] | [? ?]]; auto.

          inversion Hor as [|He'w1]; clear Hor; auto.
          assert (po_loc_llh E w1 e') as Hpollh.
            destruct Hw1e'; split; [|split]; auto.
            intros [? [? [? [? Hre']]]]; destruct Hwe' as [? [? [? Hwe']]];
            rewrite Hre' in Hwe'; inversion Hwe'.
          assert False as Ht.
            apply (Huni w1 e' Hpollh); auto; left; left; right; auto.
          inversion Ht.

      left; generalize (bin_In (fun w : Event =>
        (w = wbef E (B s1) r1 \/ B s1 (wbef E (B s1) r1) w) /\ loc r1 = loc w) w1 Hb); auto.
inversion Ht.*)

Lemma if_ld_then_lf :
  forall E X de,
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (d de) ->
  labels_of_es E X (f de).
Proof.
intros E X de Hwfl Hwfrfl Hld; case_eq de.
  intros [w r] Hde; rewrite Hde in Hld; apply if_ldr_then_lfr with E; auto.
  intros w Hde; rewrite Hde in Hld; apply if_ldw_then_lfw with E; auto.
Qed.
Lemma if_lf_then_ld :
  forall E X de,
  wf_labels E (labels_of_es E X) ->
  labels_of_es E X (f de) ->
  labels_of_es E X (d de).
Proof.
intros E X de [? [? [? Hdf]]] Hlf; auto.
Qed. 

Lemma ci0_rr :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_rs E (Rs s1) ->
  AWmm.valid_execution E X ->
  labels_of_es E X (f (DR (w1, r1))) ->
  (exists dr, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) /\
    (~(exists l' : Label,
       tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
       tc (OEL.LE (tc (X2p E X))) l' (f (DR (w1,r1)))) \/ Last.last dr = f (DR (w1,r1))) /\
     machine E dr (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1)) ->
  is_emp (Intersection Event (Rs s1)
               (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e)) = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hwfd Hwfl Hwfrfl Hwfrs Hv Hlr1 Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudrp.
case_eq (is_emp
  (Intersection Event (Rs s1)
     (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e))); intro He; auto.
generalize (is_emp_axf (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e) He);
intros [e [Hrs H1e]].
assert (reads E e) as Hre.
  apply Hwfrs; auto.
assert (exists de, labels_of_es E X (d de) /\ evt_of_devt de = e) as Hde.
  destruct Hwfrfl as [Hwfr ?]. 
  generalize (Hwfr e Hre); intros [w [Hrfm Hl]].
  exists (DR (w,e)); split; auto. 
    destruct Hwfl as [? [? [? Hfd]]]; apply Hfd; auto.
destruct Hde as [de [Hlde Hde]].
assert (events E e) as Hee.
  apply ABasic.po_iico_range_in_events with r1; auto. 
    apply tc_ppo_fences_in_po; auto.
assert (f (DR (w1, r1)) <> d de) as Hdiff.
    intro Heq; inversion Heq; auto.

assert (tc (OEL.LE (tc (X2p E X))) (d de) (f (DR (w1, r1)))) as He1.
  apply trc_step; 
  apply (in_rs_implies_d_before E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DR (w1,r1))) n s0 s1 de e phi); auto.

assert (tc (OEL.LE (tc (X2p E X))) (f (DR (w1, r1))) (d de)) as Htc1e.
  apply trc_step; apply Hi; apply trc_step; apply X2p_ppo_fences; auto. 
    rewrite Hde; auto.
    apply if_ld_then_lf; auto.
assert (tc (OEL.LE (tc (X2p E X))) (d de) (d de)) as Hc.
  apply trc_ind with (f (DR (w1,r1))); auto.
assert False as Ht.
  apply (oel_ac (X2p E X) (labels_of_es E X) Hpart (d de) Hc).
inversion Ht.
Qed.

Lemma cc0_rw :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_rs E (Rs s1) ->
  AWmm.valid_execution E X ->
  labels_of_es E X (f (DR (w1, r1))) ->
  (exists dr, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) /\
    (~(exists l' : Label,
       tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
       tc (OEL.LE (tc (X2p E X))) l' (f (DR (w1,r1)))) \/ Last.last dr = f (DR (w1,r1))) /\
     machine E dr (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1)) ->
  is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e)) = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hwfd Hwfl Hwfrfl Hwfrs Hv Hlr1 Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudrp.
case_eq (is_emp
  (Intersection _ (B s1)
     (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e))); intro Hb; auto.
generalize (is_emp_axf (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e) Hb);
intros [e [Heb H1e]].
assert (events E e) as Hee.
  apply ABasic.po_iico_range_in_events with r1; auto.
    apply tc_ppo_fences_in_po; auto.
assert (f (DR (w1, r1)) <> d (DW e)) as Hdiff.
    intro Heq; inversion Heq; auto.
assert (tc (OEL.LE (tc (X2p E X))) (d (DW e)) (f (DR (w1, r1)))) as He1.
  assert ((B s1) e) as Hudr.
    auto.
  apply trc_step;
  apply (in_buff_implies_before E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DR (w1,r1))) n s0 s1 e phi Htrans Hee Hudr); auto.
assert (tc (OEL.LE (tc (X2p E X))) (f (DR (w1, r1))) (d (DW e))) as Htc1e.
  apply trc_step; apply Hi; apply trc_step; apply X2p_ppo_fences; auto. 
    apply if_ld_then_lf; auto.
      apply Hudrp; left; exists (f (DR (w1,r1))); auto.
      rewrite trans_tc in He1; auto.
assert (tc (OEL.LE (tc (X2p E X))) (d (DW e)) (d (DW e))) as Hc.
  apply trc_ind with (f (DR (w1,r1))); auto.
assert False as Ht.
  apply (oel_ac (X2p E X) (labels_of_es E X) Hpart (d (DW e)) Hc).
inversion Ht.
Qed.

Hypothesis ppo_cc0RW :
  forall E r e,
  reads E r ->
  po_loc E r e ->
  tc (rel_union (A.ppo E) (A.fences E)) r e.

Lemma cc0_rw2 :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_rs E (Rs s1) ->
  AWmm.valid_execution E X ->
  labels_of_es E X (f (DR (w1, r1))) ->
  (exists dr, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) /\
    (~(exists l' : Label,
       tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
       tc (OEL.LE (tc (X2p E X))) l' (f (DR (w1,r1)))) \/ Last.last dr = f (DR (w1,r1))) /\
     machine E dr (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1)) ->
  is_emp (Intersection _ (B s1) (fun e : Event => po_loc E r1 e)) = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hwfd Hwfl Hwfrfl Hwfrs Hv Hlr1 Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudrp.
case_eq (is_emp
  (Intersection _ (B s1)
     (fun e : Event => po_loc E r1 e))); intro Hb; auto.
generalize (is_emp_axf (B s1) (fun e : Event => po_loc E r1 e) Hb);
intros [e [Heb H1e]].
assert (events E e) as Hee.
  apply ABasic.po_iico_range_in_events with r1; auto; destruct H1e as [? ?]; auto.
assert (f (DR (w1, r1)) <> d (DW e)) as Hdiff.
    intro Heq; inversion Heq; auto.
assert (tc (OEL.LE (tc (X2p E X))) (d (DW e)) (f (DR (w1, r1)))) as He1.
  assert ((B s1) e) as Hudr.
    auto.
  apply trc_step;
  apply (in_buff_implies_before E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DR (w1,r1))) n s0 s1 e phi Htrans Hee Hudr); auto.
assert (tc (OEL.LE (tc (X2p E X))) (f (DR (w1, r1))) (d (DW e))) as Htc1e.
  apply trc_step; apply Hi; apply trc_step; apply X2p_ppo_fences; auto.
    apply ppo_cc0RW; auto.
    inversion Hlr1 as [Hw1 | Hr1].
      destruct Hw1 as [w [Hw1 [Hc | Hc]]]; inversion Hc.
      destruct Hr1 as [w [r [Hrf [Hc | Heq]]]]. 
        inversion Hc.
        inversion Heq; subst.
        assert (rfmaps_well_formed E (events E) (rf X)) as Hrfwf.
          destruct_valid Hv; split; auto.
        split. 
          apply ABasic.ran_rf_in_events with X w; auto.
          apply ABasic.ran_rf_is_read with E X w; auto.
            destruct Hrfwf as [? [? ?]]; auto.

    apply if_ld_then_lf; auto.
      apply Hudrp; left; exists (f (DR (w1,r1))); auto.
      rewrite trans_tc in He1; auto.
assert (tc (OEL.LE (tc (X2p E X))) (d (DW e)) (d (DW e))) as Hc.
  apply trc_ind with (f (DR (w1,r1))); auto.
assert False as Ht.
  apply (oel_ac (X2p E X) (labels_of_es E X) Hpart (d (DW e)) Hc).
inversion Ht.
Qed.

Lemma freads_dont_block :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DR (w1,r1))) -> 
  wf_ws E (B s1) -> wf_rs E (Rs s1) ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DR (w1,r1)))) (labels_of_es E X) (f (DR (w1,r1))) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  ~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (f (DR (w1,r1))) phi = None).
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfl Hwfrfl Hlfwr Hwfb Hwfq Hm (*Hfifo*) Hs; simpl in Hs;
unfold flush_resolved_read_step in Hs.
assert (rf X w1 r1) as Hrf1.
  rewrite <- (rf_p2X_X2p E X Hwf Hv Hwfl); auto.
  split; auto. 
    destruct Hwfl as [? [[? Hr_f] ?]]; apply Hr_f; auto.

  assert (labels_of_es E X (f (DW w1))) as Hlw1.
    apply wfl_w with E; auto; split.
      apply ABasic.dom_rf_in_events with X r1; auto.
        destruct_valid Hv; split; auto.
      apply ABasic.dom_rf_is_write with E X r1; auto.
        destruct_valid Hv; auto.

case_eq (bin (Rs s1) r1); intro Hq; rewrite Hq in Hs.
Focus 2. (*r1 is not in Q*)
rewrite in_order_implies_rs_state with E X n s0 s1 w1 r1 phi in Hq; auto.
  inversion Hq.

  clear Hq; case_eq (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e))); 
  intro Hci0_rr; rewrite Hci0_rr in Hs.
  Focus 2.
    rewrite ci0_rr with E X n s0 s1 w1 r1 phi in Hci0_rr; inversion Hci0_rr; auto.
    exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w1, r1)))); split; [|split; [|split]]; auto.
      apply td_tpred; auto. apply oel_trans with (labels_of_es E X); auto. apply tc_X2p_partial_order; auto.
      intros x y Hxy; auto.
      left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

  clear Hci0_rr; case_eq (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e))); 
  intro Hcc0_rw; rewrite Hcc0_rw in Hs.
  Focus 2. 
    rewrite cc0_rw with E X n s0 s1 w1 r1 phi in Hcc0_rw; inversion Hcc0_rw; auto.
    exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w1, r1)))); split; [|split]; auto.
      apply td_tpred; auto. 
        apply oel_trans with (labels_of_es E X); auto. 
          apply tc_X2p_partial_order; auto.
      intros x y Hxy; auto.
      split; auto.
        left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

  unfold visible in Hs; auto; clear Hcc0_rw;
  case_eq (is_emp (Intersection _ (B s1) (fun e : Event => po_loc E r1 e))); intro Huni; rewrite Huni in Hs.
  Focus 2.
    rewrite cc0_rw2 with E X n s0 s1 w1 r1 phi in Huni; inversion Huni; auto.
    exists (pred (OEL.LE (tc (X2p E X))) (f (DR (w1, r1)))); split; [|split]; auto.
      apply td_tpred; auto. 
        apply oel_trans with (labels_of_es E X); auto. 
          apply tc_X2p_partial_order; auto.
      intros x y Hxy; auto.
      split; auto.
        left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

  destruct (eqEv_dec (wbef E (B s1) r1) dB). 
  destruct (eqEv_dec (waft E (B s1) r1) dB). 
  case_eq (bin
           (Union Event ((B s1))
              (fun e : Event => po_loc E e r1 /\ e = w1)) w1); intro Hib; rewrite Hib in Hs; [inversion Hs|].
  rewrite (ioipobs E X n s0 s1 w1 r1 phi Hwf Hv Hwfl Hwfd Hlw1 Hlfwr Hrf1 Hm) in Hib.
  inversion Hib.

       case_eq (bin (fun e : Event =>
                  phi e (waft E (B s1) r1) /\ loc r1 = loc e \/
                  po_loc E e r1 /\ e = w1) w1); intro Haft; rewrite Haft in Hs. 
        Focus 2. (*contrad uniproc ws;rf*)
        rewrite uwsrfc with E X n s0 s1 w1 r1 phi in Haft; auto; inversion Haft.
        inversion Hs.

          case_eq (bin (fun e : Event => (e = wbef E (B s1) r1 \/ phi (wbef E (B s1) r1) e) /\
            loc r1 = loc e (*\/
            po_loc E e r1 /\
            ~(exists e' : Event,
               writes E e' /\
               loc e' = loc r1 /\ po_loc E e e' /\ po_loc E e' r1) /\ 
            e = w1*)) w1); intro Hbef; rewrite Hbef in Hs.
            inversion Hs.
            destruct (eqEv_dec (waft E (B s1) r1) dB); inversion Hs.
            case_eq (bin (fun e : Event =>
              phi e (waft E (B s1) r1) /\ loc r1 = loc e \/
              po_loc E e r1 /\ e = w1) w1); intro Haft; rewrite Haft in Hs. 
        Focus 2. (*contrad uniproc ws;rf*)
        rewrite uwsrfc with E X n s0 s1 w1 r1 phi in Haft; auto; inversion Haft.
        inversion Hs.
            rewrite ufrc with E X n s0 s1 w1 r1 phi in Hbef; auto; inversion Hbef.
Qed.

Lemma long_cumul_contrad_buff :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X -> 
  wf_devts E -> wf_buff E (Rcp s1) -> wf_rs E (Rs s1) ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (f (DW w1)) ->
  labels_of_es E X (d (DR (w1,r1))) ->
  rf X w1 r1 ->
  machine E (pred (OEL.LE (tc (X2p E X))) (d (DR (w1,r1)))) (labels_of_es E X) (d (DR (w1,r1))) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  bemp (rrestrict (fun e1 e2 : Event => phi e1 e2 /\ e1 = w1) (fun e => 
    (rel_seq (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) ((hb E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))))) e r1)) = true.
Proof.
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfb Hwfq Hwfl Hwfrfl Hlfw Hldr Hrf Hm (*Hfifo*).
case_eq (bemp (rrestrict (fun e1 e2 : Event => phi e1 e2 /\ e1 = w1) (fun e => 
  (rel_seq (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) ((hb E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))))) e r1)));
intro Hb; auto.

generalize (bemp_axf (fun e1 e2 : Event => phi e1 e2 /\ e1 = w1) (fun e => 
  (rel_seq (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) ((hb E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))))) e r1) Hb); clear Hb;
intros [e [Hib Her1]].

generalize Hv; intro Hv'; destruct_valid Hv; 
generalize (tc_X2p_partial_order E X Hwf Hv' Hwfd); intro Hpart.

    assert (r1 = evt_of_devt (DR (w1,r1))) as Hdr1.
      simpl; auto.

    assert (events E w1) as Hew1.
      apply ABasic.dom_rf_in_events with X r1; auto; split; auto.
    assert (w1 <> dB) as Hdiff.
      intro Heq; apply (dB_not_in_E E w1 Hew1 Heq).


    assert (exists m, exists lst, exists s, wf_buff E (Rcp s) /\ wf_rs E (Rs s) /\
      (exists r, trans r /\ rel_incl r ((pred (OEL.LE (tc (X2p E X))) lst)) /\ 
      (~(exists l' : Label, tc (OEL.LE (tc (X2p E X))) (Last.last r) l' /\
          tc (OEL.LE (tc (X2p E X))) l' lst) \/ Last.last r = lst) /\
      machine E r (labels_of_es E X) lst m phi (Some s0) (Some s)) /\
      Rcp s w1 e) as Hex.
      apply phi_rcp; auto; destruct Hib as [? [Hphi Heq]]; rewrite Heq in Hphi; auto.

  assert (co X w1 e) as Hco.
    destruct Hex as [m [lst [s [Hwfbs [Hwfrss [Hex H1e]]]]]].
    apply rcp_ws' with E m s0 s lst phi; auto.
    destruct Hwfbs as [? [? [? [? Hsl]]]]; apply Hsl; auto.

assert False as Ht.
 apply (Hlc r1); exists e; split; auto.
  split; [|split; [|exists w1; split]]; auto.
    rewrite Hdr1; apply label_implies_evt with X (d (DR (w1,r1))); auto; split; auto.
    apply ABasic.ran_ws_in_events with X w1; auto; split; auto.

    generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htr.
    assert (exists d0, trans d0 /\ rel_incl d0 (pred (OEL.LE (tc (X2p E X))) (d (DR (w1, r1)))) /\
      (~ (exists l', tc (OEL.LE (tc (X2p E X))) (Last.last d0) l' /\
          tc (OEL.LE (tc (X2p E X))) l' (d (DR (w1, r1)))) \/
          Last.last d0 = d (DR (w1, r1))) /\
          machine E d0 (labels_of_es E X) (d (DR (w1, r1))) n phi (Some s0) (Some s1)) as Hexd.
      exists (pred (OEL.LE (tc (X2p E X))) (d (DR (w1, r1)))); split; [|split; [|split]]; auto.
        apply td_tpred; auto.
        intros e1 e2 H12; auto. 
        left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

  rewrite p2X_X2p in Her1; auto.
inversion Ht.
Qed.

Lemma ii0_rr :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_rs E (Rs s1) ->
  AWmm.valid_execution E X ->
  labels_of_es E X (d (DR (w1,r1))) ->
  (exists dr, trans dr /\ rel_incl dr (pred (OEL.LE (tc (X2p E X))) (d (DR (w1,r1)))) /\
    (~(exists l' : Label,
       tc (OEL.LE (tc (X2p E X))) (Last.last dr) l' /\
       tc (OEL.LE (tc (X2p E X))) l' (d (DR (w1,r1)))) \/ Last.last dr = d (DR (w1,r1))) /\
     machine E dr (labels_of_es E X) (d (DR (w1,r1))) n phi (Some s0) (Some s1)) ->
  is_emp
       (Intersection Event (Rs s1)
          (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e)) = true.
Proof.  
intros E X n s0 s1 w1 r1 phi Hwf Hwfd Hwfl Hwfrfl Hwfrs Hv Hlr1 Hm.
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudrp.
case_eq (is_emp
  (Intersection Event (Rs s1)
     (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e))); intro He; auto.
generalize (is_emp_axf (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e) He);
intros [e [Hrs H1e]].
assert (exists de, labels_of_es E X (d de) /\ evt_of_devt de = e) as Hde.
  generalize (Hwfrs e Hrs); intro Hre.
  destruct Hwfrfl as [Hrl ?]; generalize (Hrl e Hre).
  intros [w [Hrfm Hlf]]; exists (DR (w,e)); split; auto.
  destruct Hwfl as [? [? [? Hdf]]]; apply Hdf; auto.
destruct Hde as [de [Hlde Hde]].
generalize (tc_ppo_fences_in_po E r1 e Hwf H1e); intro Hpo.
assert (events E e) as Hee.
  apply ABasic.po_iico_range_in_events with r1; auto.
assert (d (DR (w1, r1)) <> d de) as Hdiff.
    intro Heq; inversion Heq; auto.
    rewrite <- H0 in Hde; simpl in Hde; rewrite Hde in Hpo.
    generalize Hpo; apply ABasic.po_ac; auto.

assert (tc (OEL.LE (tc (X2p E X))) (d de) (d (DR (w1, r1)))) as He1.
  apply trc_step; 
  apply (in_rs_implies_d_before E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (d (DR (w1,r1))) n s0 s1 de e phi); auto. 

assert (tc (OEL.LE (tc (X2p E X))) (d (DR (w1, r1))) (d de)) as Htc1e.
  apply trc_ind with (f (DR (w1,r1))); apply trc_step; apply Hi; apply trc_step.
    apply X2p_df; auto.  
      apply if_ldr_then_lfr with E; auto.
    apply X2p_ppo_fences; auto. 
    rewrite Hde; auto.
    apply if_ldr_then_lfr with E; auto.
    apply if_ld_then_lf; auto.

assert (tc (OEL.LE (tc (X2p E X))) (d de) (d de)) as Hc.
  apply trc_ind with (d (DR (w1,r1))); auto.
assert False as Ht.
  apply (oel_ac (X2p E X) (labels_of_es E X) Hpart (d de) Hc).
inversion Ht.
Qed.

Lemma dreads_dont_block :
  forall E X n s0 s1 w1 r1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X -> 
  wf_devts E ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X (d (DR (w1,r1))) -> 
  wf_buff E (Rcp s1) -> wf_rs E (Rs s1) ->
  machine E (pred (OEL.LE (tc (X2p E X))) (d (DR (w1,r1)))) (labels_of_es E X) (d (DR (w1,r1))) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  ~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (d (DR (w1,r1))) phi = None).
Proof. 
intros E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfl Hwfrfl Hld Hwfb Hwfq Hm (*Hfifo*) Hs; simpl in Hs;
unfold buff_read_step in Hs.

assert (labels_of_es E X (f (DR (w1,r1)))) as Hlfwr.
  inversion Hld as [[? [? [Hc | Hc]]] | [w [r [Hrf [Heq | Hc]]]]].
    inversion Hc. inversion Hc. 
    inversion Heq; right; exists w; exists r; split; auto.
    inversion Hc.

assert (rf X w1 r1) as Hrf1.
  rewrite <- (rf_p2X_X2p E X Hwf Hv Hwfl); auto.
  split; auto. 
    destruct Hwfl as [? [[? Hr_f] ?]]; apply Hr_f; auto.

  assert (labels_of_es E X (f (DW w1))) as Hlw1.
    apply wfl_w with E; auto; split.
      apply ABasic.dom_rf_in_events with X r1; auto.
        destruct_valid Hv; split; auto.
      apply ABasic.dom_rf_is_write with E X r1; auto.
        destruct_valid Hv; auto.

rewrite long_cumul_contrad_buff with E X n s0 s1 w1 r1 phi in Hs; auto.

case_eq (okw E (B s1) w1 r1);
intro Hok; rewrite Hok in Hs; [|inversion Hs].
  case_eq (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r1 e)));
  intro Hb; rewrite Hb in Hs; [|inversion Hs].
    inversion Hs.
    
    rewrite ii0_rr with E X n s0 s1 w1 r1 phi in Hb; inversion Hb; auto.
      exists (pred (OEL.LE (tc (X2p E X))) (d (DR (w1, r1)))); split; [|split; [|split]]; auto.
        apply td_tpred; auto. apply oel_trans with (labels_of_es E X); auto. apply tc_X2p_partial_order; auto.
        intros x y Hxy; auto. left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

  assert (rfmaps_well_formed E (events E) (rf X)) as Hrfwf.
    destruct_valid Hv; split; auto.
  assert ((forall e1 e2 : Event, rf X e1 e2 -> rfmaps (events E) e1 e2)) as Hrfm.
    destruct Hrfwf as [? [? ?]]; auto.
  generalize (ABasic.dom_rf_is_write E X w1 r1 Hrfm Hrf1); intros [? [? Haw]].
  generalize (ABasic.ran_rf_is_read E X w1 r1 Hrfm Hrf1); intros [? [? Har]].
  assert (w1 <> r1) as Hdiff.
    intro Heq; rewrite Heq in Haw; rewrite Haw in Har; inversion Har.
  assert (loc w1 = loc r1) as Heqloc.
      apply ABasic.rf_implies_same_loc2 with E X; auto; split; auto.
        destruct_valid Hv; split; auto.
  assert (rfe X w1 r1) as Hrfe.
    split; auto.
    intro Heq;
    generalize (ABasic.same_proc_implies_po Hwf Heq Hdiff); intros [Hwr | Hrw].
      apply ABasic.dom_rf_in_events with X r1; auto.
      apply ABasic.ran_rf_in_events with X w1; auto.
    assert (bin (fun e : Event => po_loc E e r1) w1 = true) as Hbin.
      apply In_bin; split; auto.

    unfold okw in Hok; rewrite Hbin in Hok; inversion Hok.
    
    destruct_valid Hv; unfold AWmm.uniproc in Huni;
    unfold AWmm.com_vs_po in Huni; apply (Huni r1 w1); auto.
      split; [|split]; auto.
      intros [Hr1 [? [? [? Hisrw]]]];  rewrite Haw in Hisrw; inversion Hisrw.
      left; left; left; left; auto.

  generalize (in_order_implies_mem_or_buff_state_d E X n s0 s1 w1 r1 phi Hwf Hv Hwfd Hwfl Hlw1 Hlfwr Hrfe Hm);
  intro Hran.
  assert (bin ((B s1)) w1 = true) as Hbin.
    apply In_bin; auto.
  unfold okw in Hok; rewrite Hbin in Hok; 
  destruct (bin (fun e : Event => po_loc E e r1) w1);
  inversion Hok.
Qed.

Lemma po_ws :
  forall E X w1 w2,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  writes E w1 -> writes E w2 ->
  po_iico E w1 w2 -> loc w1 = loc w2 ->
  ws X w1 w2.
Proof.
intros E X w1 w2 Hwf Hv H1 H2 Hpo Hl.
destruct_valid Hv.
destruct (eqEv_dec w1 w2) as [Heq | Hneq].

assert False as Ht.
  rewrite Heq in Hpo.
  apply (ABasic.po_ac Hwf Hpo).
inversion Ht.

assert (ws X w1 w2 \/ ws X w2 w1) as Hor.
  generalize (Hws_tot (loc w1)); intro Hlin; destruct_lin Hlin.
  assert ((writes_to_same_loc_l (events E) (loc w1)) w1) as Hw1.
    destruct H1 as [? [l [v Haw]]]; 
    split; auto; exists v; unfold loc; rewrite Haw; auto.
  assert ((writes_to_same_loc_l (events E) (loc w1)) w2) as Hw2.
    rewrite Hl; destruct H2 as [? [l [v Haw]]];  
    split; auto; exists v; unfold loc; rewrite Haw; auto.
     
  generalize (Htot w1 w2 Hneq Hw1 Hw2); intros [[? ?]|[? ?]]; auto.

inversion Hor as [| H21]; auto.

  assert (po_loc_llh E w1 w2) as Hpio.
    split; [|split]; auto.
    intros [? [? [? [? Har]]]]; destruct H2 as [? [? [? Haw]]]; rewrite Har in Haw; inversion Haw.

  assert (com' E X w2 w1) as Hhb.
    left; left; right; auto. 
  generalize (Huni w1 w2 Hpio); intro; contradiction.
Qed.

Lemma propagation :
  forall E X n s0 s1 w1 phi,
  well_formed_event_structure E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_ws E (B s1) -> wf_buff E (Rcp s1) ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  labels_of_es E X (f (DW w1)) ->
  (exists r, trans r /\ rel_incl r (pred (OEL.LE (tc (X2p E X))) (f (DW w1))) /\ 
    (~(exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (Last.last r) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (f (DW w1))) \/ Last.last r = f (DW w1)) /\
     machine E r (labels_of_es E X) (f (DW w1)) n phi (Some s0) (Some s1)) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  bemp (rrestrict
             (fun w2 w3 : Event =>
              (po_loc E w2 w3 \/
                 (A.prop E
                    (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)))
                 w2 w3) /\ w2 = w1) (fun e : Event => udr (Rcp s1) e)) = true.
Proof.
intros E X n s0 s1 w1 phi Hwf Hwfl Hwfrfl Hwfb Hwfrcp Hv Hwfd Hm Hl1 (*Hfifo*).
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudr.

case_eq (bemp
  (rrestrict
     (fun w2 w3 : Event =>
      (po_loc E w2 w3 \/
         (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)))
         w2 w3) /\ w2 = w1) (fun e : Event => udr (Rcp s1) e))); intro Hemp; auto.
generalize (bemp_axf (fun w2 w3 : Event =>
             (po_loc E w2 w3 \/
                (A.prop E
                   (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)))
                w2 w3) /\ w2 = w1) (fun e : Event => udr (Rcp s1) e) Hemp).
intros [e [[x [Hor Heq]] Hrcp]].
assert (events E e) as Hee.
  inversion Hor as [Hpo | Hprop].
    apply ABasic.po_iico_range_in_events with x; auto.
      destruct Hpo as [? ?]; auto.
    assert (tc (A.prop E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))) x e) as Htc.
      apply trc_step; auto.
    generalize (ran_prop_W E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)) x e Htc); intros [? ?]; auto.

assert (labels_of_es E X (f (DW e)) /\ evt_of_devt (DW e) = e) as Hde.
  split; auto. 
    left; exists e; split; auto.
    destruct Hwfrcp as [Hw ?]; apply Hw; auto.
      apply dB_not_in_E with E; auto.
destruct Hde as [Hlde Hde].

assert (f (DW w1) <> f (DW e)) as Hdiff.
  intro Heql; inversion Heql. 
  rewrite Heq in Hor; rewrite H0 in Hor.
  inversion Hor as [Hbee | Hcpee].
    destruct Hbee as [? Hpo]; generalize Hpo; apply ABasic.po_ac; auto.

    apply (A.prop_valid E (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X))); exists e; auto.

assert (tc (OEL.LE (tc (X2p E X))) (f (DW e)) (f (DW w1))) as Hfef1.
  apply trc_step;
  apply (in_rcp_implies_f_before E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DW w1)) n s0 s1 e phi); auto.
    (*intros w Hlw; apply Hi; apply trc_step; apply X2p_dfw; auto.*)

inversion Hor as [Hb | Hcoprop].

  assert (tc (OEL.LE (tc (X2p E X))) (f (DW e)) (f (DW e))) as Hc.
    apply trc_ind with (f (DW w1)); auto.
    apply trc_step; apply Hi; apply trc_step; apply X2p_ws; auto.
      destruct Hwfl as [[? Hfl] ?]; rewrite Heq in Hb; destruct Hb as [? ?]; apply po_ws with E; auto.
  generalize (Hacp (f (DW e)) Hc); intro Ht; inversion Ht.

  assert (tc (OEL.LE (tc (X2p E X))) (f (DW e)) (f (DW e))) as Hc.
    apply trc_ind with (f (DW w1)); auto.
    apply trc_step; apply Hi; apply trc_step; auto.
      apply X2p_prop; auto. 
        rewrite Heq in Hcoprop; rewrite p2X_X2p in Hcoprop; auto; simpl; apply trc_step; auto.
  generalize (Hacp (f (DW e)) Hc); intro Ht; inversion Ht.
Qed.

Lemma commit_before_rcp :
  forall E X n s0 s1 w1 phi,
  well_formed_event_structure E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  wf_ws E (B s1) ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  labels_of_es E X (f (DW w1)) ->
  (exists r, trans r /\ rel_incl r (pred (OEL.LE (tc (X2p E X))) (f (DW w1))) /\ 
    (~(exists l' : Label,
     tc (OEL.LE (tc (X2p E X))) (Last.last r) l' /\
     tc (OEL.LE (tc (X2p E X))) l' (f (DW w1))) \/ Last.last r = f (DW w1)) /\
     machine E r (labels_of_es E X) (f (DW w1)) n phi (Some s0) (Some s1)) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  bin ((B s1)) w1 = true.
Proof.
intros E X n s0 s1 w1 phi Hwf Hwfl Hwfrfl Hwfb Hv Hwfd Hlw Hm (*Hfifo*).
generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
generalize (oel_tot (X2p E X) (labels_of_es E X) Hpart); intro Htotp.
generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hi.
generalize (oel_ac (X2p E X) (labels_of_es E X) (tc_X2p_partial_order E X Hwf Hv Hwfd)); intro Hacp. 
generalize (oel_trans (X2p E X) (labels_of_es E X) Hpart); intro Htrans.
generalize (oel_udr (X2p E X) (labels_of_es E X) Hpart); intro Hudr.

case_eq (bin ((B s1)) w1); intro Hib; auto.
generalize (nbin_nIn ((B s1)) w1 Hib); intro Hn.
assert ((B s1) w1) as Hy.
  apply in_order_implies_in_buff with E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (f (DW w1)) n s0 (f (DW w1)) phi; auto.
    apply wfl_e; auto.
    apply Hi; apply trc_step; apply X2p_dfw; auto.
    apply Hi; apply trc_step; apply X2p_dfw; auto.
contradiction.
Qed.

Lemma fwrites_dont_block :
  forall E X n s0 s1 w1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) ->
  wf_rf_labels E (labels_of_es E X) ->
  writes E w1 -> 
  wf_ws E (B s1) -> wf_rs E (Rs s1) -> wf_buff E (Rcp s1) ->
  labels_of_es E X (f (DW w1)) ->
  machine E (pred (OEL.LE (tc (X2p E X))) (f (DW w1))) (labels_of_es E X) (f (DW w1)) n phi (Some s0) (Some s1) ->
(*  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->*)
  ~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (f (DW w1)) phi = None).
Proof.
intros E X n s0 s1 w1 phi Hwf Hv Hwfd Hwfl Hwrfl Hw Hwfb Hwfrs Hwfrcp Hlw Hm (*Hfifo*) Hs; simpl in Hs;
unfold flush_write_step in Hs.
case_eq (bin ((B s1)) w1); intro Hi; rewrite Hi in Hs; [|inversion Hs].

clear Hi; case_eq (bemp
           (rrestrict
              (fun w2 w3 : Event =>
               (po_loc E w2 w3 \/
                  (A.prop E
                     (p2X E (OEL.LE (tc (X2p E X))) (labels_of_es E X)))
                  w2 w3) /\ w2 = w1) (fun e : Event => udr (Rcp s1) e))); intro Hbemp; 
rewrite Hbemp in Hs; [|inversion Hs].

  inversion Hs.

rewrite propagation with E X n s0 s1 w1 phi in Hbemp; auto; inversion Hbemp.
  exists (pred (OEL.LE (tc (X2p E X))) (f (DW w1))); split; [|split; [|split]]; auto.
    apply td_tpred; auto. apply oel_trans with (labels_of_es E X); auto. apply tc_X2p_partial_order; auto.
    intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.

rewrite commit_before_rcp with E X n s0 s1 w1 phi in Hi; auto; inversion Hi.
  exists (pred (OEL.LE (tc (X2p E X))) (f (DW w1))); split; [|split; [|split]]; auto.
    apply td_tpred; auto. apply oel_trans with (labels_of_es E X); auto. apply tc_X2p_partial_order; auto.
    intros x y Hxy; auto.
    left; apply Last.no_interv_last; auto; intros x y Hxy; auto.
Qed.

Lemma valid_implies_not_stuck :
  forall E X l1 phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  wf_labels E (labels_of_es E X) -> wf_rf_labels E (labels_of_es E X) ->
  labels_of_es E X l1 ->
  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->
  ~((exists n, exists s0, exists s1,
   wf_ws E (B s1) /\ wf_rs E (Rs s1) /\ wf_buff E (Rcp s1) /\ wf_rs E (Cs s1) /\
   machine E (pred (OEL.LE (tc (X2p E X))) l1) (labels_of_es E X) l1 n phi (Some s0) (Some s1) /\
   step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) l1 phi = None)).
Proof.
intros E X l1 phi Hwf Hv Hwfd Hwfl Hwfrfl Hlb1 Hfifo [n [s0 [s1 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]].

  generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intro Hpart.
  generalize (oel_incl (X2p E X) (labels_of_es E X) Hpart); intro Hitc.

case_eq l1; intros de Hde.

case_eq de; intros c Hc. 
  destruct c as [w r]; subst;
  generalize Hs; fold (~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (d (DR (w,r))) phi = None));
  apply dreads_dont_block with n s0; auto.

  subst; generalize Hs; fold (~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (d (DW c)) phi = None));
  apply dwrites_dont_block with n s0; auto.
    destruct Hwfl as [[Hwdw ?] ?]; generalize (Hwdw c Hlb1); auto.

case_eq de; intros c Hc.
  destruct c as [w r]; subst; 
  generalize Hs; fold (~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (f (DR (w,r))) phi = None));
  apply freads_dont_block with n s0; auto.

    generalize (tc_X2p_partial_order E X Hwf Hv Hwfd); intros [Hudr ?].

  subst; generalize Hs; fold (~(step E (OEL.LE (tc (X2p E X))) (labels_of_es E X) (Some s1) (f (DW c)) phi = None));
  apply fwrites_dont_block with n s0; auto.
    destruct Hwfl as [[? Hwfw] ?]; generalize (Hwfw c Hlb1); auto.
Qed.

Definition mns E p (L:set Label) phi :=
  forall l, L l -> (p l (Last.last p) \/ Last.last p = l) ->
  ~((exists n, exists s0, exists s1,
   wf_ws E (B s1) /\ wf_rs E (Rs s1) /\ wf_buff E (Rcp s1) /\ wf_rs E (Cs s1) /\
   machine E (pred p l) L l n phi (Some s0) (Some s1) /\
   step E p L (Some s1) l phi = None)).

Lemma vexec_forms_path :
  forall E X phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->
  mns E (OEL.LE (tc (X2p E X)))(labels_of_es E X) phi.
Proof.
intros E X phi Hwf Hv Hwfd Hfifo l1 Hlb1 Hllb1.
  apply valid_implies_not_stuck; auto.
  apply wfl_es; auto.
  apply wfl_rf_es; auto.
Qed.

Lemma mp :
  forall E p l L n s0 s1 phi,
  Included _ (Union _ (dom p) (ran p)) L ->
  (forall d, rel_incl d p ->
     (forall x1 x2, x1 <> x2 -> (L x1 /\ udr d x1) -> (L x2 /\ udr d x2) ->
      d x1 x2 \/ d x2 x1)) -> 
  (exists d, d = (pred p l) /\ 
     machine E d L l n phi (Some s0) (Some s1)) ->
  machine E (pred p l) L l n phi (Some s0) (Some s1).
Proof.
intros E p l L n s0 s2 phi Hudr Htot Hm;
generalize p l s2 Hudr Htot Hm; clear p l s2 Hudr Htot Hm;
induction n; intros p l s2 Hudr Htot [d [Hi Hm]].

  inversion Hm.
    subst; auto.

  assert (rel_incl d (pred p l)) as Hincl.
     rewrite Hi; intros x y Hxy; auto.          

  destruct Hm as [l' [s1 [Hl' [Hm [Hs [Hwfs ?]]]]]];
  fold (machine E (pred d l') L l' n phi (Some s0) (Some s1)) in Hm.
    exists l'; exists s1; split; [|split; [|split; [|split]]]; auto.  
      subst; auto.  
      rewrite <- Hi; auto.
    
  assert (exists d : Rln Label,
    d = (pred (pred p l) l') /\
    machine E d L l' n phi (Some s0) (Some s1)) as Hex'.
    exists (pred d l'); split; auto.
      rewrite Hi; auto.
 
  assert (forall d : Rln Label,
  rel_incl d (pred p l) ->
  forall x1 x2 : Label,
  x1 <> x2 -> L x1 /\ udr d x1 -> L x2 /\ udr d x2 -> d x1 x2 \/ d x2 x1) as Htot'.
    intros d0 Hi0 x1 x2 Hdiff H1 H2; apply (Htot d0); auto.
      apply rel_incl_trans with (pred p l); auto; apply pred_incl; auto.

  assert (Included Label (Union Label (dom (pred p l)) (ran (pred p l))) L) as Hudr'.
    apply incl_trans with (Union _ (dom p) (ran p)); auto.
    intros ? [x [y [Hxy ?]] | x [y [Hyx ?]]].
      left; exists y; auto. right; exists y; auto.

  generalize (IHn (pred p l) l' s1 Hudr' Htot' Hex'); intro Hm'; auto.

      apply step_monot with d; auto.
Qed.

Lemma mns_pred :
  forall E p (L:set Label) l phi,
  Included _ (Union _ (dom p) (ran p)) L ->
  trans p ->
  L l ->
  (forall d, rel_incl d p ->
     (forall x1 x2, x1 <> x2 -> (L x1 /\ udr d x1) -> (L x2 /\ udr d x2) ->
      d x1 x2 \/ d x2 x1)) -> 
  mns E p L phi ->
  mns E (pred p l) L phi.
Proof.
intros E p L l phi Hudrp Htp Hl Htotp Hmns l' Hl' Hll'.
intros [n [s0 [s1 [Hwfb [Hwfq [Hwfrcp [Hwfcs [Hm Hs]]]]]]]].
  
  assert (rel_incl (pred p l) p) as Hincl.
    intros x y [Hxy ?]; auto.

apply (Hmns l' Hl').

  destruct (eqLabel_dec l (Last.last p)) as [Heql | Hneql].
  rewrite <- Heql; left.
    inversion Hll' as [Hpred | Hlast]; clear Hll'.
    destruct Hpred as [? ?].
      apply Htp with (Last.last (pred p l)); auto.
      generalize (Last.last_in_ran (pred p l) l' Hlast); intros [? [? ?]]; auto.

  assert (p (Last.last (pred p l)) (Last.last p)) as Hpp.
      assert (Last.last (pred p l) = Last.last (pred p l)) as Ht.
        auto.
      generalize (Last.last_in_ran (pred p l) (Last.last (pred p l)) Ht); intros [x [? ?]]; auto;
      apply Htp with l; auto.
      assert (p l (Last.last p) \/ p (Last.last p) l) as Hor.
        assert (rel_incl p p) as Hi.
          intros e1 e2 H12; auto.
        assert (L l /\ udr p l) as Hll.
          split; auto; right; exists (Last.last (pred p l)); auto.
        assert (L (Last.last p) /\ udr p (Last.last p)) as Hllp.
          split; auto.
            apply Hudrp; right; apply Last.last_in_ran; auto.
            right; apply Last.last_in_ran; auto.
        generalize (Htotp p Hi l (Last.last p) Hneql Hll Hllp); auto.

      inversion Hor as [|Hc]; clear Hor; auto.
        assert (Last.last p = Last.last p) as Htlp.
          auto.
        generalize (Last.last_is_last p (Last.last p) Htlp); intro Hn.
        assert (exists l' : Label, p (Last.last p) l') as Hy.
          exists l; auto.
        contradiction.

  left; inversion Hll' as [Hpred | Hlast]; clear Hll'.
    destruct Hpred as [? ?].
      apply Htp with (Last.last (pred p l)); auto.
      rewrite <- Hlast; auto.

  exists n; exists s0; exists s1; 
    split; [|split; [|split; [|split; [|split]]]]; auto.

    apply mp; auto.
      exists (pred (pred p l) l'); split; auto.

      apply pred_pred; auto.  
      inversion Hll' as [Hpred | Hlast]; clear Hll'.
        destruct Hpred as [? ?].
          apply Htp with (Last.last (pred p l)); auto.
          generalize (Last.last_in_ran (pred p l) l' Hlast); intros [? [? ?]]; auto.

  apply step_monot with (pred p l); auto.
Qed.

Lemma some_none :
  forall E p L s1 l phi,
  step E p L (Some s1) l phi <> None ->
  (exists s2 : State, step E p L (Some s1) l phi = Some s2).
Proof.
intros E p L s1 l phi Hn.
case_eq (step E p L (Some s1) l phi). 
  intros s Hss.
  exists s; auto.

  intros Hns; contradiction.
Qed.

Lemma delb_trans :
  forall (B:Rln Event) w,
  trans B ->
  trans (del_buff B w).
Proof.
intros B w Htr; unfold del_buff; intros e1 e2 e3 [H12 [? ?]] [H23 [? ?]];
split; [|split]; auto; apply Htr with e2; auto.  
Qed.

Lemma tc_delb :
  forall B w e x y,
  tc ((rrestrict (del_buff B w) (fun w0 : Event => loc w0 = loc e))) x y ->
  tc ((rrestrict B (fun w0 : Event => loc w0 = loc e))) x y.
Proof.
intros B w e x y Hxy.
induction Hxy as [x y [[Hs ?] ?]|].

  apply trc_step; split; auto.

  apply trc_ind with z; auto.
Qed.

Lemma delb_ac :
  forall B w,
  (forall e, acyclic (rrestrict B (fun w : Event => loc w = loc e))) ->
  (forall e, acyclic (rrestrict (del_buff B w) (fun w0 : Event => loc w0 = loc e))).
Proof.
intros B w Hac e x Hx.
generalize (tc_delb B w e x x Hx); intro Hc.
apply (Hac e x Hc); auto.
Qed.

Lemma wfb_fwd :
  forall E p L s1 s2 l phi,
  wf_labels E L ->
  wf_rf_labels E L ->
  L l ->
  wf_ws E (B s1) ->
  step E p L (Some s1) l phi = Some s2 ->
  wf_ws E (B s2).
Proof.
intros E p L s1 s2 l phi Hwfl Hwfrfl Hll Hwfb Hs.
case_eq l; intros de Hl; rewrite Hl in Hs;
case_eq de.
  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_read_step in Hs.   
  destruct (okw E (B s1) w r); [|inversion Hs];
  destruct (is_emp (Intersection Event (Rs s1)
              (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r))); 
  inversion Hs; simpl; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_write_step in Hs.
  destruct (is_emp (Intersection Event (Rs s1) (fun r' : Event => (A.fences E) w r'))); [|inversion Hs].
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs].
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => (A.prop E (p2X E p L)) w e))); [|inversion Hs].
  inversion Hs; simpl; auto.
  unfold wf_ws in * |- *; unfold upd_rs; auto.
    intros ? [e Hb | e Hw]; auto.
      inversion Hw.
      destruct Hwfl as [[Hdw ?] ?]; apply Hdw; auto.
        rewrite Hde in Hl; rewrite Hl in Hll; auto.

  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; unfold flush_resolved_read_step in Hs.
    destruct (bin (Rs s1) r); [|inversion Hs]; auto.
    destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];  
    destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs]; auto.
      inversion Hs; simpl; auto.
      destruct (visible E s1 w r phi); inversion Hs; simpl; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold flush_write_step in Hs.
  destruct (bin (B s1) w); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => (po_loc E w1 w2  \/ (A.prop E (p2X E p L)) w1 w2) /\ w1 = w)
              (fun e : Event => udr (Rcp s1) e))); [|inversion Hs].
  inversion Hs; simpl; auto.
Qed. 

Lemma wfq_fwd :
  forall E p L s1 s2 l phi,
  wf_labels E L -> wf_rf_labels E L ->
  L l ->
  wf_rs E (Rs s1) ->
  step E p L (Some s1) l phi = Some s2 ->
  wf_rs E (Rs s2).
Proof.
intros E p L s1 s2 l phi Hwfl Hwfrfl Hil Hwfq Hs.
case_eq l; intros de Hl; rewrite Hl in Hs;
case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_read_step in Hs.
 
  destruct (okw E (B s1) w r); [|inversion Hs];
  destruct (is_emp (Intersection Event (Rs s1)
              (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r))); inversion Hs; simpl; auto.

  intros e [e' He|e' He].
    apply Hwfq; auto.
    destruct Hwfl as [? [[Hd ?] ?]].
    rewrite He; rewrite Hde in Hl; rewrite Hl in Hil; generalize (Hd w r Hil);
    intros [? [? [a [? [[v Har] ?]]]]]; split; auto; exists a; exists v; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_write_step in Hs.
  destruct (is_emp
           (Intersection Event (Rs s1)
              (fun r' : Event => (A.fences E) w r'))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs].
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => (A.prop E (p2X E p L)) w e))); [|inversion Hs].
  inversion Hs; auto.

  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; simpl; auto.
  unfold flush_resolved_read_step in Hs.
    destruct (bin (Rs s1) r); [|inversion Hs]; auto.
    destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
    destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs]; auto.
    destruct (visible E s1 w r phi); inversion Hs; simpl; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold flush_write_step in Hs.
  destruct (bin (B s1) w); [|inversion Hs].
  destruct (bemp  (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
               w1 = w) (fun e : Event => udr (Rcp s1) e))); [|inversion Hs].
  inversion Hs; auto.
Qed.

Lemma wfrcp_fwd :
  forall E p L s1 s2 l phi,
  wf_labels E L -> wf_rf_labels E L ->
  L l ->
  wf_buff E (Rcp s1) ->
  step E p L (Some s1) l phi = Some s2 ->
  wf_buff E (Rcp s2).
Proof.
intros E p L s1 s2 l phi Hwfl Hwfrfl Hil Hwfq Hs.
case_eq l; intros de Hl; rewrite Hl in Hs;
case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_read_step in Hs.
 
  destruct (okw E (B s1) w r); [|inversion Hs];
  destruct (is_emp (Intersection Event (Rs s1)
              (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r))); inversion Hs; simpl; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_write_step in Hs.
  destruct (is_emp
           (Intersection Event (Rs s1)
              (fun r' : Event => (A.fences E) w r'))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs].
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => (A.prop E (p2X E p L)) w e))); [|inversion Hs].
  inversion Hs; auto.

  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; simpl; auto.
  unfold flush_resolved_read_step in Hs.
    destruct (bin (Rs s1) r); [|inversion Hs]; auto.
    destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
    destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs]; auto.
    destruct (visible E s1 w r phi); inversion Hs; simpl; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold flush_write_step in Hs.
  destruct (bin (B s1) w); [|inversion Hs].
  destruct (bemp  (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
               w1 = w) (fun e : Event => udr (Rcp s1) e))); [|inversion Hs].
  inversion Hs; auto.
  simpl.
  apply wfb_upd with L; auto.
    assert (evt_of_label l = w) as Heq.
      rewrite Hl; rewrite Hde; auto.
    rewrite <- Heq; apply wfl_e with L; auto.
    destruct Hwfl as [? [? [? Hdf]]]; apply Hdf;
    rewrite <- Hde; rewrite <- Hl; auto.
Qed.

Inductive length (p:Rln Label) (L:set Label) lst n : Prop :=
  | Zero : n = 0 -> False -> length p L lst n 
  | Succ : forall m l, n = S m -> L l -> 
    Last.last p = l ->
    length (pred p l) L l m -> length p L lst n. 

Lemma wfcs_fwd :
  forall E p L s1 s2 l phi,
  wf_labels E L -> wf_rf_labels E L ->
  L l ->
  wf_rs E (Cs s1) ->
  step E p L (Some s1) l phi = Some s2 ->
  wf_rs E (Cs s2).
Proof.
intros E p L s1 s2 l phi Hwfl Hwfrfl Hil Hwfq Hs.
case_eq l; intros de Hl; rewrite Hl in Hs;
case_eq de.

  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_read_step in Hs.
 
  destruct (okw E (B s1) w r); [|inversion Hs];
  destruct (is_emp (Intersection Event (Rs s1)
              (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs].
  destruct (bemp (rrestrict (fun w1 w2 : Event => phi w1 w2 /\ w1 = w) (fun e => rel_seq (A.prop E (p2X E p L)) ((*rc*) (hb E (p2X E p L))) e r))); inversion Hs; simpl; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold buff_write_step in Hs.
  destruct (is_emp
           (Intersection Event (Rs s1)
              (fun r' : Event => (A.fences E) w r'))); [|inversion Hs];
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => po_iico E w e /\ loc w = loc e))); [|inversion Hs].
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => (A.prop E (p2X E p L)) w e))); [|inversion Hs].
  inversion Hs; auto.

  intros [w r] Hde; rewrite Hde in Hs; simpl in Hs; simpl; auto.
  unfold flush_resolved_read_step in Hs.
    destruct (bin (Rs s1) r); [|inversion Hs]; auto.
    destruct (is_emp (Intersection Event (Rs s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs];
    destruct (is_emp (Intersection _ (B s1) (fun e : Event => tc (rel_union (A.ppo E) (A.fences E)) r e))); [|inversion Hs]; auto.
  unfold visible in Hs;
  destruct (is_emp (Intersection _ (B s1) (fun e : Event => po_loc E r e))); [|inversion Hs]; auto.
  destruct (eqEv_dec (wbef E (B s1) r) dB) as [Heb | Hneb]; [|inversion Hs].
  destruct (eqEv_dec (waft E (B s1) r) dB) as [Hab | Hnab]; [|inversion Hs].
  destruct (bin (Union Event ((B s1)) (fun e : Event => po_loc E e r /\ e = w)) w); [|inversion Hs].
  inversion Hs; simpl; auto.

  intros e [e' He|e' He].
    apply Hwfq; auto.
    destruct Hwfl as [? [[? Hd] ?]].
    rewrite He; rewrite Hde in Hl; rewrite Hl in Hil; generalize (Hd w r Hil);
    intros [? [? [a [? [[v Har] ?]]]]]; split; auto; exists a; exists v; auto.

  destruct (bin (fun e : Event =>
            phi e (waft E (B s1) r) /\ loc r = loc e \/
            po_loc E e r /\ e = w) w); 
  inversion Hs; simpl; auto.
  intros e [e' He|e' He].
    apply Hwfq; auto.
    destruct Hwfl as [? [[? Hd] ?]].
    rewrite He; rewrite Hde in Hl; rewrite Hl in Hil; generalize (Hd w r Hil);
    intros [? [? [a [? [[v Har] ?]]]]]; split; auto; exists a; exists v; auto.

  destruct (bin (fun e : Event =>
            (e = wbef E (B s1) r \/ phi (wbef E (B s1) r) e) /\
            loc r = loc e) w); [|inversion Hs].
  destruct (eqEv_dec (waft E (B s1) r) dB) as [Hab | Hnab]; [|inversion Hs].
  inversion Hs; simpl; auto. 
  intros e [e' He|e' He].
    apply Hwfq; auto.
    destruct Hwfl as [? [[? Hd] ?]].
    rewrite He; rewrite Hde in Hl; rewrite Hl in Hil; generalize (Hd w r Hil);
    intros [? [? [a [? [[v Har] ?]]]]]; split; auto; exists a; exists v; auto.

  destruct (bin (fun e : Event =>
            phi e (waft E (B s1) r) /\ loc r = loc e \/
            po_loc E e r /\ e = w) w); 
  inversion Hs; simpl; auto.
  intros e [e' He|e' He].
    apply Hwfq; auto.
    destruct Hwfl as [? [[? Hd] ?]].
    rewrite He; rewrite Hde in Hl; rewrite Hl in Hil; generalize (Hd w r Hil);
    intros [? [? [a [? [[v Har] ?]]]]]; split; auto; exists a; exists v; auto.

  intros w Hde; rewrite Hde in Hs; simpl in Hs; unfold flush_write_step in Hs.
  destruct (bin (B s1) w); [|inversion Hs].
  destruct (bemp  (rrestrict
              (fun w1 w2 : Event =>
               (po_loc E w1 w2 \/ (A.prop E (p2X E p L)) w1 w2) /\
               w1 = w) (fun e : Event => udr (Rcp s1) e))); [|inversion Hs].
  inversion Hs; auto.
Qed.

Lemma progress :
  forall E p (L:set Label) lst phi,
  wf_labels E L -> wf_rf_labels E L ->
  Included _ (Union Label (dom p) (ran p)) L ->
  trans p ->
  (forall d, rel_incl d p ->
     (forall x1 x2, x1 <> x2 -> (L x1 /\ udr d x1) -> (L x2 /\ udr d x2) ->
      d x1 x2 \/ d x2 x1)) ->
  (exists n, length p L lst n) ->
  mns E p L phi -> 
  ((exists n, exists s0, exists s1, 
    wf_ws E (B s1) /\ wf_rs E (Rs s1) /\ wf_buff E (Rcp s1) /\ wf_rs E (Cs s1) /\
    machine E p L lst n phi (Some s0) (Some s1))).
Proof.
intros E p L lst phi Hwfl Hwfrfl Hudrp Htp Htotp [n Hn].
induction Hn as [p L l n Heqn Hf | p L lx n m l Heqn Hl Hdp].

  inversion Hf.

  intros Hmns.

  assert (mns E (pred p l) L phi) as Hmnspred.
    apply mns_pred; auto.

  assert (Included Label (Union Label (dom (pred p l)) (ran (pred p l))) L) as Hudrpp.
    intros ? [x [y [Hx ?]] | x [y [Hx ?]]]; apply Hudrp; [left | right]; exists y; auto.

  assert (forall d : Rln Label,
        rel_incl d (pred p l) ->
        forall x1 x2 : Label,
        x1 <> x2 ->
        L x1 /\ udr d x1 -> L x2 /\ udr d x2 -> 
        d x1 x2 \/ d x2 x1) as Htotpp.
    intros d Hincl x1 x2 Hdiff [Hl1 ?] [Hl2 ?]; apply Htotp; auto.
      intros x y Hxy; apply Hincl; auto.

  generalize (IHHn Hwfl Hwfrfl Hudrpp (td_tpred p l Htp) Htotpp Hmnspred); 
  intros [n0 [s0 [s1 [Hwfb [Hwfq [Hwfrcp [Hwfcs Hm]]]]]]]; clear IHHn.
  generalize (Hmns l Hl); intro Hno.
  assert (forall n s0 s1, 
            wf_ws E (B s1) ->
            wf_rs E (Rs s1) ->
            wf_buff E (Rcp s1) ->
            wf_rs E (Cs s1) ->
            machine E (pred p l) L l n phi (Some s0) (Some s1) ->
            ~(step E p L (Some s1) l phi = None)) as Hfall.
    intros n' s s' Hwfb' Hwfq' Hwfrcp' Hwfcs' Hm' Hsn.
    assert (p l (Last.last p) \/ Last.last p = l) as Hlast.
      destruct Hdp; auto.
    apply (Hno Hlast); exists n'; exists s; exists s'; split; [|split; [|split]]; auto.
  clear Hno.
  generalize (Hfall n0 s0 s1 Hwfb Hwfq Hwfrcp Hwfcs Hm); intro Hnnone.
    exists (S n0); exists s0.
    
    generalize (some_none E p L s1 l phi Hnnone); intros [s2 Hs2].
    exists s2; split; [|split; [|split; [|split]]].

      apply wfb_fwd with p L s1 l phi; auto. 
      apply wfq_fwd with p L s1 l phi; auto.
      apply wfrcp_fwd with p L s1 l phi; auto.
      apply wfcs_fwd with p L s1 l phi; auto.

      exists l; exists s1; split; [|split; [|split; [|split]]]; auto.
Qed.

Definition wf_l_lp p (L:set Label) :=
  forall l, L l ->
  (p l (Last.last p) \/ Last.last p = l).  

Lemma mns_progress_mns:
  forall E p (L:set Label) phi,
  wf_l_lp p L ->
  (forall l, L l -> 
   (exists n, exists s0, exists s1, 
    wf_ws E (B s1) /\ wf_rs E (Rs s1) /\ wf_buff E (Rcp s1) /\ wf_rs E (Cs s1) /\
    machine E (pred p l) L l n phi (Some s0) (Some s1))) ->
  mns E p L phi ->
  machine_not_stuck E p L phi.
Proof.
intros E p L phi Hwflp Hprogress Hmns l Hl;
generalize (Hwflp l Hl); intro Hlast;
generalize (Hmns l Hl Hlast); intro Hn.

assert (exists n : nat,
         exists s0 : State,
           exists s1 : State,
               wf_ws E (B s1) /\
               wf_rs E (Rs s1) /\
               wf_buff E (Rcp s1) /\
               wf_rs E (Cs s1) /\
               machine E (pred p l) L l n phi (Some s0) (Some s1) /\
               (exists s2, step E p L (Some s1) l phi = Some s2)) as Hex.
  generalize (Hprogress l Hl); intros [n [s0 [s1 [Hwfb [Hwfq [Hwfrcp [Hwfcs Hm]]]]]]](*]*);
  exists n; exists s0; exists s1; split; [|split; [|split; [|split; [|split]]]]; auto.
  generalize (excluded_middle (step E p L (Some s1) l phi = None)); intros [Hnone | Hsome]; auto.
    assert False as Ht.
      apply Hn; exists n; exists s0; exists s1; split; [|split; [|split; [|split]]]; auto.
    inversion Ht.

    generalize (excluded_middle (exists s2, step E p L (Some s1) l phi = Some s2)); 
      intros [He | Hne]; auto.
    
    apply (some_none E p L s1 l phi Hsome).

destruct Hex as [n [s0 [s1 [Hwfm [Hwfb [Hwfq [Hwfrcp [Hwfcs [s2 Hs12]]]]]]]]];
exists n; exists s0; exists s1; exists s2; split; [|split; [|split]]; auto.
Qed.

Lemma mns_mns :
  forall E p (L:set Label) phi,
  wf_labels E L -> wf_rf_labels E L -> wf_l_lp p L ->
  Included Label (Union Label (dom p) (ran p)) L ->
  trans p ->
  (forall d0 : Rln Label,
   rel_incl d0 p ->
   forall x1 x2 : Label,
   x1 <> x2 -> L x1 /\ udr d0 x1 -> L x2 /\ udr d0 x2 -> 
   d0 x1 x2 \/ d0 x2 x1) ->
  (forall l, L l -> exists n, length (pred p l) L l n) ->
  mns E p L phi ->
  machine_not_stuck E p L phi.
Proof.
intros E p L phi Hwfl Hwfrfl Hwflp Hudrp Htp Htotp Hfp Hllp Hmns; apply mns_progress_mns; auto.
intros l Hl; apply progress; auto.
  intros ? [x [y [Hx ?]]|x [y [Hx ?]]]; apply Hudrp;
    [left|right]; exists y; auto. 
  apply td_tpred; auto.

    intros d Hi; apply Htotp.
      intros e1 e2 H12; generalize (Hi e1 e2 H12); intros [? ?]; auto.

apply mns_pred; auto.
Qed.

Definition pred_tot E X :=
(forall d0 : Rln Label,
rel_incl d0 (OEL.LE (tc (X2p E X))) ->
forall x1 x2 : Label,
x1 <> x2 ->
labels_of_es E X x1 /\ udr d0 x1 ->
labels_of_es E X x2 /\ udr d0 x2 -> d0 x1 x2 \/ d0 x2 x1).

Definition fpref E X :=
(forall l : Label, labels_of_es E X l ->
  (exists n : nat,
    length (pred (OEL.LE (tc (X2p E X))) l) (labels_of_es E X) l n)) /\
wf_l_lp (OEL.LE (tc (X2p E X))) (labels_of_es E X) /\
pred_tot E X.

Theorem from_ax_to_mach :
  forall E X phi,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  wf_devts E ->
  (forall w1 w2, OEL.LE (tc (X2p E X)) (f (DW w1)) (f (DW w2)) -> OEL.LE (tc (X2p E X)) (d (DW w1)) (d (DW w2))) ->
  fpref E X ->
  machine_not_stuck E (OEL.LE (tc (X2p E X)))(labels_of_es E X) phi.
Proof.
intros E X phi Hwf Hv Hwfd Hfifo [? [? ?]].
generalize (tc_X2p_partial_order E X Hwf Hv); intro Hpart.
apply mns_mns; auto.
  apply wfl_es; auto.
  apply wfl_rf_es; auto.
  apply oel_udr; auto.
  apply oel_trans with (labels_of_es E X); auto.

intros l1 Hlb1 ?.
  apply valid_implies_not_stuck; auto.
  apply wfl_es; auto.
  apply wfl_rf_es; auto.
Qed.

End Completeness.