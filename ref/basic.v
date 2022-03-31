Require Import Ensembles.
Require Import Arith.
Require Import util.
Require Import wmm.
Require Import Classical_Prop.
(*Import OEEvt. *)

Set Implicit Arguments.

Module Basic (A : Archi) (dp: Dp).
Import A.
Import dp.
Module AWmm := Wmm A dp.
Import AWmm.

Section Ax.

(** evts *)

Lemma read_write_contrad :
  forall x l1 l2,
  ~(write_to x l1 /\ read_from x l2).
Proof.
unfold write_to; unfold read_from;
intros x l1 l2 [[v1 Hw ] [v2 Hr]].
rewrite Hw in Hr; inversion Hr.
Qed.

Lemma write_to_implies_writes: (*basic*)
  forall E x l,
  (events E) x ->
  write_to x l -> 
  (writes E) x.
Proof.
intros E x l He (*[v*) Hw(*]*); unfold writes; split; auto.
exists l; (*exists v;*) auto.
Qed.

Lemma read_from_implies_reads: (*basic*)
  forall E x l,
  (events E) x ->
  read_from x l -> 
  (reads E) x.
Proof.
intros E x l He (*[v*) Hw(*]*); unfold reads; split; auto.
exists l; (*exists v;*) auto.
Qed.

Lemma read_from_implies_same_loc :
  forall x l1 l2,
  read_from x l1 ->
  read_from x l2 ->
  l1 = l2.
Proof.
unfold read_from;
intros x l1 l2 [v1 H1] [v2 H2].
rewrite H1 in H2; inversion H2; auto.
Qed.

Lemma rf_implies_same_loc :
  forall E X w y l,
(*  valid_execution E X ->*)
  rfmaps_well_formed E (events E) (rf X) ->
  rf X w y ->
  read_from y l ->
  write_to w l.
Proof.
intros E X w y l Hv Hrf Hr.
destruct(*_valid*) Hv as [? [Hrf_cands ?]].
generalize (Hrf_cands w y Hrf); intros [? [? [l' [Hw [Hr' ?]]]]].
generalize (read_from_implies_same_loc Hr Hr'); intro Heq; subst; auto.
Qed.

Lemma rf_implies_same_loc2 :
  forall E X w y,
  coherence_well_formed (events E) (co X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rf X w y ->
  loc w = loc y.
Proof.
intros E X w y [Hwswf Hrfwf] Hrf.
destruct Hrfwf as [? [Hrf_cands ?]].
generalize (Hrf_cands w y Hrf); intros [? [? [l [[v1 Hw] [[v2 Hr] ?]]]]].
unfold loc; rewrite Hw; rewrite Hr; auto.
Qed.

Lemma write_to_implies_this_loc :
  forall y l,
  write_to y l ->
  loc y = (*Some*) l.
Proof.
intros x l [v Hw]; unfold loc; rewrite Hw; auto.
Qed.

Lemma ws_implies_same_loc :
  forall E X w y,
  coherence_well_formed (events E) (co X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  co X w y ->
  loc w = loc y.
Proof.
intros E X w y [Hwswf Hrfwf] Hws.
destruct Hwswf as [? Hl].
generalize (Hl w y Hws); intros [l [[? Hw] [? Hy]]].
rewrite (write_to_implies_this_loc Hw);
rewrite (write_to_implies_this_loc Hy); trivial.
Qed.

Lemma fr_implies_same_loc :
  forall E X w y,
  coherence_well_formed (events E) (co X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  fr E X w y ->
  loc w = loc y.
Proof.
intros E X w y Hs [Hw [Hy [wr [Hrf Hws]]]].
rewrite <- (ws_implies_same_loc X wr y Hs); auto.
eapply sym_eq.
eapply rf_implies_same_loc2; [apply Hs | apply Hrf].
Qed.

Lemma fr_implies_same_loc2 :
  forall E X x y l,
  valid_execution E X ->
  fr E X x y ->
  read_from x l ->
  write_to y l.
Proof.
intros E X x y l Hv [Hew [Hey [z [Hrf Hws]]]] Hr.
destruct_valid Hv.
generalize (Hws_cands z y Hws); intros [ly [[? Hwz] [? Hwy]]].
assert (coherence_well_formed (events E) (co X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hand.
  split; split; auto.
generalize (rf_implies_same_loc2 X z x Hand Hrf); intro Heq.
  unfold read_from in Hr; unfold write_to in Hwz.
  destruct Hr as [Hvx Hax]; destruct Hwz as [Hvz Haz].
  unfold loc in Heq; rewrite Hax in Heq; rewrite Haz in Heq; 
  inversion Heq as [Hl]; rewrite <- Hl; auto.
Qed.

Lemma read_from_implies_this_loc :
  forall y l,
  read_from y l ->
  loc y = (*Some*) l.
Proof.
intros x l [v Hw].
unfold loc; rewrite Hw; auto.
Qed.

Lemma write_to_implies_same_loc :
  forall y l1 l2 v,
  action y = Access W l1 v ->
  write_to y l2 ->
  l1 = l2.
Proof.
unfold write_to;
intros x l1 l2 v H1 [v2 H2 ].
rewrite H1 in H2; inversion H2.
trivial.
Qed.

Lemma write_implies_write_to :
  forall x l v,
  action x = Access W l v ->
  write_to x l.
Proof.
intros x l v Hx; unfold write_to; exists v; auto.
Qed.

(** po *)

Lemma pos_trans :
  forall E x y z,
  (po_strict E) x y ->
  (po_strict E) y z ->
  (po_strict E) x z.
Proof.
unfold po_strict;
intros E x y z [Hpxy [Hinf_xy [Hex Hey]]] [Hpyz [Hinf_yz [Heyb Hez]]].
split; [rewrite Hpxy; rewrite Hpyz; trivial |
  split; [ | split; [apply Hex | apply Hez]]].
eapply Lt.lt_trans; [apply Hinf_xy | apply Hinf_yz].
Qed.

Lemma po_iico_trans :
  forall E x y z,
  well_formed_event_structure E ->
  (po_strict E) x y ->
  (iico E) y z ->
  (po_strict E) x z.
Proof.
unfold po_strict;
intros E x y z Hwf [Hpxy [Hinf_xy [Hex Hey]]] Hyz.
unfold well_formed_event_structure in Hwf.
destruct Hwf as [? [? [? [? [? [? [Heq ?]]]]]]].
generalize (Heq y z Hyz); intro Heqi.
rewrite <- Heqi.
  split; [apply Hpxy | split; [apply Hinf_xy |
    split; [apply Hex | ]]].
apply H2; exists y; apply Hyz.
Qed.

Lemma iico_po_trans :
  forall E x y z,
  well_formed_event_structure E ->
  (iico E) x y ->
  (po_strict E) y z ->
  (po_strict E) x z.
Proof.
unfold po_strict;
intros E x y z Hwf Hxy [Hpyz [Hinf_yz [Hey Hez]]].
unfold well_formed_event_structure in Hwf.
destruct Hwf as [? [? [? [? [? [? [Heq ?]]]]]]].
generalize (Heq x y Hxy); intro Heqi.
rewrite Heqi.
  split; [apply Hpyz | split; [apply Hinf_yz |
    split; [ | apply Hez]]].
apply H1; exists y; apply Hxy.
Qed.

Lemma iico_trans :
  forall E x y z,
  well_formed_event_structure E ->
  (iico E) x y ->
  (iico E) y z ->
  (iico E) x z.
Proof.
intros E x y z Hwf Hxy Hyz.
destruct Hwf as [? [? [? [? [? [? [? Htrans]]]]]]].
unfold util.trans in Htrans; apply (Htrans x y z Hxy Hyz).
Qed.

Lemma po_trans :
  forall E x y z,
  well_formed_event_structure E ->
  (po_iico E) x y ->
  (po_iico E) y z ->
  (po_iico E) x z.
Proof.
unfold po_iico;
intros E x y z Hwf Hxy Hyz.
inversion Hxy as [Hpo_xy | Hiico_xy];
inversion Hyz as [Hpo_yz | Hiico_yz].
  left; eapply pos_trans; eauto.
  left; eapply po_iico_trans; eauto.
  left; eapply iico_po_trans; eauto.
  right; eapply iico_trans; eauto.
Qed.

Lemma po_ac :
  forall E x, 
  well_formed_event_structure E ->
  ~((po_iico E) x x).
Proof.
unfold not;
intros E x Hwf Hpo_iico.
unfold well_formed_event_structure in Hwf.
destruct Hwf as [? [? [? [? [Hac ?]]]]].
inversion Hpo_iico as [Hpo | Hiico].
  unfold po_strict in Hpo.
  destruct Hpo as [? [Hinf [? ?]]].
  generalize (Gt.gt_irrefl (poi (iiid x))); intro Hc.
  contradiction.
  unfold util.acyclic in Hac; apply (Hac x);
    apply util.trc_step; apply Hiico.
Qed.

Lemma diff_proc_implies_not_po :
  forall E x y,
  well_formed_event_structure E ->
  proc_of x <> proc_of y ->
  ~(po_iico E x y).
Proof.
intros E x y Hwf Hdiff Hxy.
inversion Hxy as [Hpo | Hiico].
  destruct Hpo as [Hpr ?].
    unfold not in Hdiff; unfold proc_of in Hdiff.
    apply (Hdiff Hpr).
destruct Hwf as [? [? [? [? [? [? [Heq ?]]]]]]].
  generalize (Heq x y Hiico); intro Heqi.
  unfold proc_of in Hdiff; unfold not in Hdiff; rewrite Heqi in Hdiff;
  apply Hdiff; auto.
Qed.

Lemma same_proc_implies_po :
  forall E x y,
  well_formed_event_structure E ->
  proc_of x = proc_of y -> x <> y ->
  In _ (events E) x -> In _ (events E) y ->
  po_iico E x y \/ po_iico E y x.
Proof.
intros E x y Hwf Heqp Hd Hex Hey.
  destruct (Arith.Compare_dec.lt_eq_lt_dec x.(iiid).(poi) y.(iiid).(poi)) as [Horb | Hsup].
    inversion Horb as [Hinf | Heq].
    left; left; split; auto.
    left; right.
      destruct Hwf as [? [? [? [? [? [Hii ?]]]]]].
      assert (events E x /\ events E y /\ poi (iiid x) = poi (iiid y) /\ proc_of x = proc_of y) as Hand.
        split; [|split; [|split]]; auto.
      apply (Hii x y Hand); auto.
  right; left; split; auto.
Qed.

Lemma po_implies_same_proc :
  forall E x y,
  well_formed_event_structure E ->
  In _ (events E) x -> In _ (events E) y ->
  po_iico E x y -> proc_of x = proc_of y.
Proof.
intros E x y Hwf Hex Hey Hpo_xy.
      destruct Hwf as [Ht ?].
  apply Ht; auto.
Qed.

(** ws*)

Lemma ws_cands :
  forall E X x e,
  coherence_well_formed (events E) (co X) ->
  co X x e ->
  exists l : Location,
    In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) e.
Proof.
intros E X x e Hv Hws.
destruct Hv as [? Hws_cands]; apply (Hws_cands x e Hws).
Qed.

Lemma ws_cy :
  forall E X x,
  (forall l : Location,
          util.linear_strict_order
            (util.rrestrict (co X) (writes_to_same_loc_l (events E) l))
            (writes_to_same_loc_l (events E) l)) ->
  (forall x e, co X x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) e)) ->
  ~(co X x x).
Proof.
intros E X x Hl Hcands.
unfold not; intro Hws;
generalize (Hcands x x Hws); intros [lx [[Hex Hwx] ?]].
destruct (Hl lx) as [Hdr [Htrans [Hac Htot]]].
generalize (Hac x); intro Hn.
 unfold not in Hn; apply Hn; split;
  [apply Hws | unfold In; unfold writes_to_same_loc_l].
split; [split; [apply Hex | apply Hwx] |
 split; [apply Hex | apply Hwx]].
Qed.

Lemma ws_evt_right :
  forall E X x y,
  (forall l : Location,
          util.linear_strict_order
            (util.rrestrict (co X) (writes_to_same_loc_l (events E) l))
            (writes_to_same_loc_l (events E) l)) ->  
  (forall x e, co X x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) e)) ->
  co X x y ->
  In _ (events E) y.
Proof.
intros E X x y Hlin Hcands Hws.
generalize (Hcands x y Hws); intros [l [[Hex Hwx] [Hey Hwy]]];
apply Hey.
Qed.

Lemma ws_evt_left :
  forall E X x y,
  (forall l : Location,
          util.linear_strict_order
            (util.rrestrict (co X) (writes_to_same_loc_l (events E) l))
            (writes_to_same_loc_l (events E) l)) ->  
  (forall x e, co X x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) e)) ->
  co X x y ->
  In _ (events E) x.
Proof.
intros E X x y Hlin Hcands Hws.
generalize (Hcands x y Hws); intros [l [[Hex Hwx] [Hey Hwy]]];
apply Hex.
Qed.

Lemma ws_right :
  forall E X x y,
  (forall l : Location,
          util.linear_strict_order
            (util.rrestrict (co X) (writes_to_same_loc_l (events E) l))
            (writes_to_same_loc_l (events E) l)) ->  
  (forall x e, co X x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) e)) ->
  co X x y ->
  exists v, exists l, action y = Access W l v.
Proof.
intros E X x y Hlin Hcands Hws.
generalize (Hcands x y Hws); intros [l [[Hex Hwx] [Hey Hwy]]].
case_eq (action y).
 intros d ly v Hy.
 case_eq d.
   intro Hr; unfold write_to in Hwy; rewrite Hy in Hwy; rewrite Hr in Hwy; 
     destruct Hwy as [vy Hwy]; inversion Hwy.
   intro Hw; exists v; exists ly; trivial.
Qed.

Lemma dom_ws_is_write :
  forall E X x y,
  coherence_well_formed (events E) (co X) ->
  co X x y ->
  exists l, exists v, action x = Access W l v.
Proof.
intros E X x y [? Hws_cands] Hws.
generalize (Hws_cands x y Hws); intros [l [[Hex Hwx] [Hey Hwy]]].
case_eq (action x).
 intros d lx v Hx.
 case_eq d.
   intro Hr; unfold write_to in Hwx; rewrite Hx in Hwx; rewrite Hr in Hwx;
     destruct Hwx as [vx Hwx]; inversion Hwx.
   intro Hw; exists lx; exists v; trivial.
Qed.

Lemma ran_ws_is_write :
  forall E X x y,
  coherence_well_formed (events E) (co X) ->
  co X x y ->
  exists v, exists l, action y = Access W l v.
Proof.
intros E X x y [Hws_tot Hws_cands] Hws.
apply (ws_right E X x y Hws_tot Hws_cands Hws).
Qed.

Lemma ws_trans :
  forall E X x y z,
  coherence_well_formed (events E) (co X) ->
  co X x y -> co X y z ->
  co X x z.
Proof.
intros E X x y z [Hws_tot Hws_cands] Hxy Hyz.
generalize (ws_right E X x y Hws_tot Hws_cands Hxy); intros [v [l Hy]].
generalize (Hws_tot l); intros [Hdr [Htrans [Hac Htot]]].
assert (util.rrestrict (ws X) (writes_to_same_loc_l (events E) l) x y) as Hxyb.
  split; [apply Hxy |].
  generalize (Hws_cands x y Hxy); intros [lx [Hlx Hlxy]].
  generalize Hlxy; intro Hlxyb.
  destruct Hlxy as [? Hwlxy].
  generalize (write_to_implies_same_loc Hy Hwlxy); intro Heq.
  rewrite Heq; split; auto.
assert (util.rrestrict (ws X) (writes_to_same_loc_l (events E) l) y z) as Hyzb.
  split; [apply Hyz |].
destruct Hxyb as [? [? Hly]].
  split; [apply Hly |]. 
  generalize (Hws_cands y z Hyz); intros [ly [Hlyy Hlyz]].
  destruct Hlyy as [? Hwlyy].
  generalize (write_to_implies_same_loc Hy Hwlyy); intro Heq.
  rewrite Heq; auto.
assert (util.rrestrict (ws X) (writes_to_same_loc_l (events E) l) x y /\
  util.rrestrict (ws X) (writes_to_same_loc_l (events E) l) y z) as Hand.
  split; auto.
generalize (Htrans x y z Hand); intros [Hxz ?].
auto.
Qed.

(** rf *)

Lemma dom_rf_is_write :
  forall E X x y,
  (forall e1 e2 : Event, rf X e1 e2 -> rfmaps (events E) e1 e2) ->
  rf X x y ->
  exists l, exists v, action x = Access W l v.
Proof.
intros E X x y Hrf_cands Hxy.
case_eq (action x).
  intros dx lx vx Hx.
    case_eq dx.
    intro Hr.
      generalize (Hrf_cands x y Hxy); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold write_to in Hwx; rewrite Hx in Hwx; rewrite Hr in Hwx; 
      destruct Hwx as [v Hwx]; inversion Hwx.
    intro Hw; rewrite Hw in Hx.
     exists lx; exists vx; trivial.
Qed.

Lemma ran_rf_is_read :
  forall E X x y,
  (forall e1 e2 : Event, rf X e1 e2 -> rfmaps (events E) e1 e2) ->
  rf X x y ->
  exists l, exists v, action y = Access R l v.
Proof.
intros E X x y Hrf_cands Hxy.
case_eq (action y).
  intros dy ly vy Hy.
    case_eq dy.
    intro Hr; rewrite Hr in Hy.
     exists ly; exists vy; trivial.
    intro Hw.
      generalize (Hrf_cands x y Hxy); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold read_from in Hry; rewrite Hy in Hry; rewrite Hw in Hry; 
      destruct Hry as [[v Hry] ?]; inversion Hry.
Qed.

Lemma rf_uni :
  forall E X x w1 w2,
  rfmaps_well_formed E (events E) (rf X) ->
  rf X w1 x -> rf X w2 x ->
  w1 = w2.
Proof.
intros E X x w1 w2 Hrfwf Hxy.
destruct Hrfwf as [? [? Hrf_uni]].
apply Hrf_uni; [apply Hxy].
Qed.

Lemma dom_rf_in_events :
  forall E X x e,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (rf X) x e ->
  In _ (events E) x.
Proof.
intros E X x e Hwf Hrfwf Hrf.
destruct Hrfwf as [? [Hrf_cands ?]].
generalize (Hrf_cands x e Hrf); unfold rfmaps; intro Hrfmap.
destruct Hrfmap as [Hevt_x Hrest]; exact Hevt_x.
Qed.
  
Lemma ran_rf_in_events :
  forall E X x e,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (rf X) x e ->
  In _ (events E) e.
Proof.
intros E X x e Hwf Hrfwf Hrf.
destruct Hrfwf as [? [Hrf_cands ?]].
generalize (Hrf_cands x e Hrf); unfold rfmaps; intro Hrfmap.
destruct Hrfmap as [Hevt_x [Hevt_e Hrest]]; exact Hevt_e.
Qed. 

(*mrf*)

(*Lemma dom_mrf_is_write :
  forall E X x y,
  (forall e1 e2 : Event, rf X e1 e2 -> rfmaps (events E) e1 e2) ->
  mrf X x y ->
  exists l, exists v, action x = Access W l v.
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra; unfold mrf;
unfold mrfi; unfold mrfe; rewrite Hinter; rewrite Hintra; 
intros E X x y Hrf_cands Hxy; simpl in Hxy; inversion Hxy as [Hrfi | Hrfe].
case_eq (action x).
  intros dx lx vx Hx.
    case_eq dx.
    intro Hr.
      destruct Hrfi as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold write_to in Hwx; rewrite Hx in Hwx; rewrite Hr in Hwx; 
      destruct Hwx as [v Hwx]; inversion Hwx.
    intro Hw; rewrite Hw in Hx.
     exists lx; exists vx; trivial.
case_eq (action x).
  intros dx lx vx Hx.
    case_eq dx.
    intro Hr.
      destruct Hrfe as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold write_to in Hwx; rewrite Hx in Hwx; rewrite Hr in Hwx; 
      destruct Hwx as [v Hwx]; inversion Hwx.
    intro Hw; rewrite Hw in Hx.
     exists lx; exists vx; trivial.

inversion Hrfi.
case_eq (action x).
  intros dx lx vx Hx.
    case_eq dx.
    intro Hr.
      destruct Hrfe as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold write_to in Hwx; rewrite Hx in Hwx; rewrite Hr in Hwx; 
      destruct Hwx as [v Hwx]; inversion Hwx.
    intro Hw; rewrite Hw in Hx.
     exists lx; exists vx; trivial.

case_eq (action x).
  intros dx lx vx Hx.
    case_eq dx.
    intro Hr.
      destruct Hrfi as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold write_to in Hwx; rewrite Hx in Hwx; rewrite Hr in Hwx; 
      destruct Hwx as [v Hwx]; inversion Hwx.
    intro Hw; rewrite Hw in Hx.
     exists lx; exists vx; trivial.
inversion Hrfe.

inversion Hrfi.
inversion Hrfe.
Qed.

Lemma ran_mrf_is_read :
  forall E X x y,
  (forall e1 e2 : Event, rf X e1 e2 -> rfmaps (events E) e1 e2) ->
  mrf X x y ->
  exists l, exists v, action y = Access R l v.
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra; unfold mrf;
unfold mrfi; unfold mrfe; rewrite Hinter; rewrite Hintra; 
intros E X x y Hrf_cands Hxy; simpl in Hxy; inversion Hxy as [Hrfi | Hrfe].

case_eq (action y).
  intros dy ly vy Hy.
    case_eq dy.
    intro Hr; rewrite Hr in Hy.
     exists ly; exists vy; trivial.
    intro Hw.
      destruct Hrfi as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold read_from in Hry; rewrite Hy in Hry; rewrite Hw in Hry; 
      destruct Hry as [[v Hry] ?]; inversion Hry.
case_eq (action y).
  intros dy ly vy Hy.
    case_eq dy.
    intro Hr; rewrite Hr in Hy.
     exists ly; exists vy; trivial.
    intro Hw.
      destruct Hrfe as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold read_from in Hry; rewrite Hy in Hry; rewrite Hw in Hry; 
      destruct Hry as [[v Hry] ?]; inversion Hry.

inversion Hrfi.
case_eq (action y).
  intros dy ly vy Hy.
    case_eq dy.
    intro Hr; rewrite Hr in Hy.
     exists ly; exists vy; trivial.
    intro Hw.
      destruct Hrfe as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold read_from in Hry; rewrite Hy in Hry; rewrite Hw in Hry; 
      destruct Hry as [[v Hry] ?]; inversion Hry.

case_eq (action y).
  intros dy ly vy Hy.
    case_eq dy.
    intro Hr; rewrite Hr in Hy.
     exists ly; exists vy; trivial.
    intro Hw.
      destruct Hrfi as [Hrf ?].
      generalize (Hrf_cands x y Hrf); intro Hc.
      destruct Hc as [? [? [? [Hwx Hry]]]].
      unfold read_from in Hry; rewrite Hy in Hry; rewrite Hw in Hry; 
      destruct Hry as [[v Hry] ?]; inversion Hry.
inversion Hrfe.

inversion Hrfi.
inversion Hrfe.
Qed.

Lemma mrf_uni :
  forall E X x w1 w2,
  rfmaps_well_formed E (events E) (rf X) ->
  mrf X w1 x -> mrf X w2 x ->
  w1 = w2.
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra; unfold mrf;
unfold mrfi; unfold mrfe; rewrite Hinter; rewrite Hintra; simpl;
intros E X x w1 w2 Hrfwf H1 H2; destruct Hrfwf as [? [? Hrf_uni]];
inversion H1 as [Hrfi1 | Hrfe1]; inversion H2 as [Hrfi2 | Hrfe2].

destruct Hrfi1 as [Hrf1 ?]; destruct Hrfi2 as [Hrf2 ?];
apply (Hrf_uni x w1 w2 Hrf1 Hrf2).
destruct Hrfi1 as [Hrf1 ?]; destruct Hrfe2 as [Hrf2 ?];
apply (Hrf_uni x w1 w2 Hrf1 Hrf2).
destruct Hrfe1 as [Hrf1 ?]; destruct Hrfi2 as [Hrf2 ?];
apply (Hrf_uni x w1 w2 Hrf1 Hrf2).
destruct Hrfe1 as [Hrf1 ?]; destruct Hrfe2 as [Hrf2 ?];
apply (Hrf_uni x w1 w2 Hrf1 Hrf2).

inversion Hrfi1.
inversion Hrfi1.
inversion Hrfi2.
destruct Hrfe1 as [Hrf1 ?]; destruct Hrfe2 as [Hrf2 ?];
apply (Hrf_uni x w1 w2 Hrf1 Hrf2).
destruct Hrfi1 as [Hrf1 ?]; destruct Hrfi2 as [Hrf2 ?];
apply (Hrf_uni x w1 w2 Hrf1 Hrf2).

inversion Hrfe2.
inversion Hrfe1.
inversion Hrfe2.
inversion Hrfi2.
inversion Hrfe2.
inversion Hrfi2.
inversion Hrfe2.
Qed.

Lemma mrf_rf_uni :
  forall E X x w1 w2,
  rfmaps_well_formed E (events E) (rf X) ->
  mrf X w1 x -> rf X w2 x ->
  w1 = w2.
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra; unfold mrf;
unfold mrfi; unfold mrfe; rewrite Hinter; rewrite Hintra; simpl;
intros E X x w1 w2 Hrfwf H1 Hrf2; destruct Hrfwf as [? [? Hrf_uni]];
inversion H1 as [Hrfi1 | Hrfe1].

destruct Hrfi1 as [Hrf1 ?]; apply (Hrf_uni x w1 w2 Hrf1 Hrf2).
destruct Hrfe1 as [Hrf1 ?]; apply (Hrf_uni x w1 w2 Hrf1 Hrf2).

inversion Hrfi1.
destruct Hrfe1 as [Hrf1 ?]; apply (Hrf_uni x w1 w2 Hrf1 Hrf2).
destruct Hrfi1 as [Hrf1 ?]; apply (Hrf_uni x w1 w2 Hrf1 Hrf2).

inversion Hrfe1.
inversion Hrfi1.
inversion Hrfe1.
Qed.*)

(** fr *)

Lemma fr_ax1 :
  forall E X x y,
  fr E X x y ->
  exists wr, rf X wr x /\ ws X wr y.
Proof.
intros E X x y Hxy.
destruct Hxy as [? [? Hxy]]; auto.
Qed. 

Lemma fr_ax2 :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (exists wr, rf X wr x /\ ws X wr y) ->
  fr E X x y.
Proof.
intros E X x y Hwf Hvalid Hxy.
generalize Hvalid; intro Hv.
destruct Hvalid as [Hwswf Hrfwf].
destruct Hxy as [? [Hrf Hws]]; split; [| split].
eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
destruct Hwswf as [Hws_tot Hws_cands].
eapply ws_evt_right; [apply Hws_tot | apply Hws_cands | apply Hws].
exists x0; auto.
Qed.

Lemma dom_fr_is_read :
  forall E X x y,
  rfmaps_well_formed E (events E) (rf X) ->
  fr E X x y ->
  exists l, exists v, action x = Access R l v.
Proof.
intros E X x y Hvalid Hxy.
generalize (fr_ax1 Hxy); intros [? [Hrf Hws]].
destruct Hvalid as [? [Hrf_cands ?]].
eapply ran_rf_is_read; [apply Hrf_cands | apply Hrf].
Qed.

Lemma ran_fr_is_write :
  forall E X x y,
  write_serialization_well_formed (events E) (ws X) ->
  fr E X x y ->
  exists v, exists l, action y = Access W l v.
Proof.
intros E X x y Hvalid Hxy.
generalize (fr_ax1 Hxy); intros [? [Hrf Hws]].
eapply ran_ws_is_write; [apply Hvalid | apply Hws].
Qed.

End Ax.

Section DomRan.

(** po *)

Lemma po_strict_domain_in_events : forall (E:Event_struct) (e e0:Event),
  (po_strict E) e e0 ->
  In _ (events E) e.
Proof.
unfold po_strict; unfold In; intros E e e0 Hin.
destruct Hin as [Hproc [Hpoi [He He0]]].
exact He.
Qed.

Lemma po_strict_range_in_events : forall (E:Event_struct) (e e0:Event),
  (po_strict E) e e0 ->
  In _ (events E) e0.
Proof.
unfold po_strict; unfold In; intros E e e0 Hin.
destruct Hin as [Hproc [Hpoi [He He0]]].
exact He0.
Qed.

(** iico *)

Lemma iico_domain_incl_in_events : forall (E:Event_struct) (e e0: Event),
  (well_formed_event_structure E) ->
  iico E e e0 -> In _ (events E) e.

Proof.

unfold well_formed_event_structure.

intros E e e0 Hwf.
destruct Hwf as [? Hwf].
destruct Hwf as [Hsame_eiid_iiid Hwf].
destruct Hwf as [Hdomain_intra Hwf].
destruct Hwf as [Hrange_intra Hwf].
intros He_in_range_intra.

assert (In _ (util.dom (iico E)) e).
unfold util.ran; unfold In; exists e0; apply He_in_range_intra.
unfold Included in Hdomain_intra; apply Hdomain_intra; exact H0.
Qed.

Lemma iico_range_incl_in_events : forall (E:Event_struct) (e e0: Event),
  (well_formed_event_structure E) ->
  iico E e e0 -> In _ (events E) e0.
Proof.
unfold well_formed_event_structure.
intros E e e0 Hwf.
destruct Hwf as [? Hwf].
destruct Hwf as [Hsame_eiid_iiid Hwf].
destruct Hwf as [Hdomain_intra Hwf].
destruct Hwf as [Hrange_intra Hwf].
intros He0_in_domain_intra.
assert (In _ (util.ran (iico E)) e0).
unfold util.range; unfold In; exists e; exact He0_in_domain_intra.
unfold Included in Hrange_intra; apply Hrange_intra; exact H0.
Qed.

(** po_iico *)

Lemma po_iico_domain_in_events : forall (E:Event_struct) (e e0:Event),
  (well_formed_event_structure E) ->
  (po_iico E) e e0 -> In _ (events E) e.
Proof.
intros E e e0 Hwf Hpo_iico.
unfold In in Hpo_iico; unfold po_iico in Hpo_iico.
inversion Hpo_iico as [Hpo | Hiico].
eapply po_strict_domain_in_events; apply Hpo.
eapply iico_domain_incl_in_events; [exact Hwf | apply Hiico].
Qed.

Lemma po_iico_range_in_events : forall (E:Event_struct) (e e0:Event),
  (well_formed_event_structure E) ->
  (po_iico E) e e0 -> In Event (events E) e0.
Proof.
intros E e e0 Hwf Hpo_iico.
unfold In in Hpo_iico; unfold po_iico in Hpo_iico.
inversion Hpo_iico as [Hpo | Hiico].
eapply po_strict_range_in_events; apply Hpo.
eapply iico_range_incl_in_events; [exact Hwf | apply Hiico].
Qed.

Lemma com_ran_in_evts :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (com E X) y x ->
  In _ (events E) x.
Proof.
intros E X x y Hwf [Hwswf Hrfwf] Hhb.
destruct Hwswf as [Hws_tot Hws_cands];
destruct Hrfwf as [? [Hrf_cands ?]].
inversion Hhb as [Hrf_fr | Hws].
  inversion Hrf_fr as [Hrf | Hfr].
    generalize (Hrf_cands y x Hrf); intro Hrfm.
    destruct Hrfm as [Hy [Hx Hrfm]]; apply Hx.
    destruct Hfr as [Hy [Hx Hrest]]; apply Hx.
  eapply ws_evt_right.
    apply Hws_tot. (*ws ax*)
    apply Hws_cands.
    apply Hws.
Qed.

Lemma com_dom_in_evts :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (com E X) x y ->
  In _ (events E) x.
Proof.
intros E X x y Hwf [Hwswf Hrfwf] Hhb.
destruct Hwswf as [Hws_tot Hws_cands];
destruct Hrfwf as [? [Hrf_cands ?]].
inversion Hhb as [Hrf_fr | Hws].
  inversion Hrf_fr as [Hrf | Hfr].
    generalize (Hrf_cands x y Hrf); intro Hrfm.
    destruct Hrfm as [Hx [Hy Hrfm]]; apply Hx.
    destruct Hfr as [Hx [Hy Hrest]]; apply Hx.
  eapply ws_evt_left.
    apply Hws_tot. (*ws ax*)
    apply Hws_cands.
    apply Hws.
Qed.

Lemma dom_ws_in_events : 
  forall E X x e,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) ->
  (ws X) x e ->
  In _ (events E) x.
Proof.
intros E X x e Hwf Hwswf Hws.
generalize (ws_cands E X x e Hwswf Hws); intro Hmem.
destruct Hmem as [l [Hmx Hme]].
destruct Hmx as [Hdr Hrest].
unfold util.udr in Hdr.
auto.
Qed.
  
Lemma ran_ws_in_events : 
  forall E X x e,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) ->
  (ws X) x e ->
  In _ (events E) e.
Proof.
intros E X x e Hwf Hwswf Hws.
generalize (ws_cands E X x e Hwswf Hws); intro Hmem.
destruct Hmem as [l [Hmx Hme]].
destruct Hme as [Hdr Hrest].
auto.
Qed.

Lemma dom_fr_in_events : 
  forall E X x e,
  well_formed_event_structure E ->
  (fr E X) x e ->
  In _ (events E) x.
Proof.
intros E X x e Hwf Hfr.
unfold In in Hfr; unfold fr in Hfr; unfold frmaps in Hfr.
destruct Hfr as [Hevt_x Hrest].
exact Hevt_x.
Qed.
  
Lemma ran_fr_in_events : 
  forall E X x e,
  well_formed_event_structure E ->
  (fr E X) x e ->
  In _ (events E) e.
Proof.
intros E X x e Hwf Hfr.
unfold In in Hfr; unfold fr in Hfr; unfold frmaps in Hfr.
destruct Hfr as [Hevt_x [Hevt_e Hrest]].
exact Hevt_e.
Qed.

(*Lemma com_domain_in_events : forall (E:Event_struct) (X:Execution_witness) (e e0:Event),
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (com E X) e e0 -> In _ (events E) e.
Proof.
intros E X e e0 Hwf Hvalid Hhb.
inversion Hhb as [Hrf_fr | Hws].
  inversion Hrf_fr as [Hrf | Hfr].
  (*rf*)
  destruct Hvalid as [Hwswf Hrfwf];
  eapply dom_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
  (*fr*)
  eapply dom_fr_in_events; [apply Hwf | apply Hfr].
  (*ws*)
  destruct Hvalid as [Hwswf Hrfwf];
  eapply dom_ws_in_events; [apply Hwf | apply Hwswf | apply Hws].
Qed.

Lemma hb_range_in_events : forall (E:Event_struct) (X:Execution_witness) (e e0:Event),
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (hb E X) e e0 -> In _ (events E) e0.
Proof.
intros E X e e0 Hwf Hs Hhb.
inversion Hhb as [Hrf_fr | Hws].
  inversion Hrf_fr as [Hrf | Hfr].
  (*rf*)
  destruct Hs as [Hwswf Hrfwf];
  eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
  (*fr*)
  eapply ran_fr_in_events; [apply Hwf | apply Hfr].
  (*ws*)
  destruct Hs as [Hwswf Hrfwf];
  eapply ran_ws_in_events; [apply Hwf | apply Hwswf | apply Hws].
Qed.

Lemma ghb_domain_in_events : forall (E:Event_struct) (X:Execution_witness) (e e0:Event),
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (ghb E X) e e0 -> In _ (events E) e.
Proof.
intros E X e e0 Hwf Hvalid Hghb; unfold ghb in Hghb.
case_eq inter; case_eq intra; intros Hintra Hinter; 
  rewrite Hinter in Hghb; rewrite Hintra in Hghb.
  (*true true*)
  inversion Hghb as [Hrf_inter | Hrest].
    destruct Hrf_inter as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
    eapply dom_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
    inversion Hrest as [Hrf_intra | Hres].
      destruct Hrf_intra as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
      eapply dom_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
      inversion Hres as [Hin_ab | Hre].
      destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab); intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply dom_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
            (*eapply dom_fr_in_events; [apply Hwf | apply Hfr].*)
        eapply po_iico_domain_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
  (*true false*)
  inversion Hghb as [Hrf_inter | Hrest].
    destruct Hrf_inter as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
    eapply dom_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
      inversion Hrest as [Hin_ab | Hre].
      destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab); intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply dom_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
            (*eapply dom_fr_in_events; [apply Hwf | apply Hfr].*)
        eapply po_iico_domain_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
  (*false true*)
  inversion Hghb as [Hrf_intra | Hres].
      destruct Hrf_intra as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
      eapply dom_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
      inversion Hres as [Hin_ab | Hre].
  destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab); intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply dom_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
            (*eapply dom_fr_in_events; [apply Hwf | apply Hfr].*)
        eapply po_iico_domain_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
  (*false false*)
  inversion Hghb as [Hin_ab | Hre].
  destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab);  intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply dom_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
            (*eapply dom_fr_in_events; [apply Hwf  | apply Hfr].*)
        eapply po_iico_domain_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
Qed.

Lemma ghb_range_in_events : forall (E:Event_struct) (X:Execution_witness) (e e0:Event),
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (ghb E X) e e0 -> In _ (events E) e0.
Proof.
intros E X e e0 Hwf Hvalid Hghb; unfold ghb in Hghb.
case_eq inter; case_eq intra; intros Hintra Hinter; 
  rewrite Hinter in Hghb; rewrite Hintra in Hghb.
  (*true true*)
  inversion Hghb as [Hrf_inter | Hrest].
    destruct Hrf_inter as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
    eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
    inversion Hrest as [Hrf_intra | Hres].
      destruct Hrf_intra as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
      eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
      inversion Hres as [Hin_ab | Hre].
  destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab);  intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply ran_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
           (* eapply ran_fr_in_events; [apply Hwf | apply Hfr].*)
        eapply po_iico_range_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
  (*true false*)
  inversion Hghb as [Hrf_inter | Hrest].
    destruct Hrf_inter as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
    eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
      inversion Hrest as [Hin_ab | Hre].
  destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab);  intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply ran_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
           (* eapply ran_fr_in_events; [apply Hwf | apply Hfr].*)
        eapply po_iico_range_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
  (*false true*)
  inversion Hghb as [Hrf_intra | Hres].
      destruct Hrf_intra as [Hrf ?].
  destruct Hvalid as [Hwswf Hrfwf];
      eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
      inversion Hres as [Hin_ab | Hre].
  destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab);  intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply ran_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
            (*eapply ran_fr_in_events; [apply Hwf | apply Hfr].*)
        eapply po_iico_range_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
  (*false false*)
  inversion Hghb as [Hin_ab | Hre].
  destruct Hvalid as [Hwswf Hrfwf];
        generalize (ab_evts Hwf Hrfwf Hin_ab); intros [He He0]; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
  destruct Hvalid as [Hwswf Hrfwf];
            eapply ran_ws_in_events; [apply Hwf | apply Hwswf | apply Hws_fr].
            (*eapply ran_fr_in_events; [apply Hwf | apply Hfr].*)
        eapply po_iico_range_in_events; [apply Hwf |].
          apply ppo_valid; apply Hppo.
Qed.

Lemma ghb_in_evts :
  forall E X,
  (well_formed_event_structure E) ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  Included _
    (Union _ (util.dom (ghb E X)) (util.ran (ghb E X))) (events E).
Proof.
unfold Included; unfold util.domain; unfold util.range; unfold In;
intros E X Hwf Hvalid x Hx.
inversion Hx as [e Hdom | e Hran]; 
  [unfold In in Hdom; destruct Hdom as [x0 Hdom] | 
   unfold In in Hran; destruct Hran as [x0 Hran]].
  (*dom*)
    change (events E x) with (In _ (events E) x); 
    eapply ghb_domain_in_events; [apply Hwf | apply Hvalid | apply Hdom].
  (*ran*)
    change (events E x) with (In _ (events E) x); 
    eapply ghb_range_in_events; [apply Hwf | apply Hvalid | apply Hran].
Qed.

Lemma mrf_in_ghb :
  forall E X x y, 
  mrf X x y ->
  ghb E X x y.
Proof.
intros E X x y Hrf.
inversion Hrf as [Hi | He];
case_eq inter; case_eq intra; intros Hinter Hintra; 
  unfold ghb; rewrite Hinter; rewrite Hintra.
  unfold mrfi in Hi; rewrite Hinter in Hi.
  right; left; apply Hi.
  unfold mrfi in Hi; rewrite Hinter in Hi; inversion Hi.
  unfold mrfi in Hi; rewrite Hinter in Hi.
  left; apply Hi.
  unfold mrfi in Hi; rewrite Hinter in Hi; inversion Hi.
  unfold mrfe in He; rewrite Hintra in He.
  left; apply He.  
  unfold mrfe in He; rewrite Hintra in He.
  left; apply He. 
  unfold mrfe in He; rewrite Hintra in He; inversion He.
  unfold mrfe in He; rewrite Hintra in He; inversion He.
Qed.

Lemma ws_in_ghb :
  forall E X x y, 
  ws X x y ->
  ghb E X x y.
Proof.
intros E X x y Hws.
case_eq inter; case_eq intra; intros Hinter Hintra; 
  unfold ghb; rewrite Hinter; rewrite Hintra.
  right; right; right; left; (*left;*) auto.
  right; right; left; (*left;*) auto.
  right; right; left; (*left;*) auto.
  right; left; (*left;*) auto.
Qed.*)

(*Lemma fr_in_ghb :
  forall E X x y, 
  fr E X x y ->
  ghb E X x y.
Proof.
intros E X x y Hfr.
case_eq inter; case_eq intra; intros Hinter Hintra; 
  unfold ghb; rewrite Hinter; rewrite Hintra.
  right; right; right; left; right; auto.
  right; right; left; right; auto.
  right; right; left; right; auto.
  right; left; right; auto.
Qed.*)

(*Lemma ppo_in_ghb :
  forall E X x y, 
  ppo E x y ->
  ghb E X x y.
Proof.
intros E X x y Hppo.
case_eq inter; case_eq intra; intros Hinter Hintra; 
  unfold ghb; rewrite Hinter; rewrite Hintra.
  right; right; right; right; auto.
  right; right; right; auto.
  right; right; right; auto.
  right; right; auto.
Qed.*)

(*Lemma ws_ax2 : 
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  util.tc (ghb E X) x y ->
  (exists l : Location,
       In _
         (writes_to_same_loc_l
            (util.udr (util.tc (ghb E X))) l) y /\
       In _
         (writes_to_same_loc_l
            (util.udr (util.tc (ghb E X))) l) x) ->
  ws X x y.
Proof.
intros E X x y Hwf Hvalid Htc Hl.
generalize Hvalid; intro Hv.
    destruct_valid Hvalid; assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
      split; split; auto.
destruct Hl as [l [Hy Hx]].
assert (In _ (writes_to_same_loc_l (events E) l) y) as Hmy.
  split; destruct Hy as [Hy Hw]; [|apply Hw].
    generalize (ghb_in_evts X Hwf Hs); intro Hi; unfold Included in Hi;
    apply Hi.
    generalize (util.dom_ran_tc (ghb E X)); intro Heq; rewrite Heq; auto.
assert (In _ (writes_to_same_loc_l (events E) l) x) as Hmx.
  split; destruct Hx as [Hx Hw]; [|apply Hw].

    generalize (ghb_in_evts X Hwf Hs); intro Hi; unfold Included in Hi;
    apply Hi.
    generalize (util.dom_ran_tc (ghb E X)); intro Heq; rewrite Heq; auto.
generalize (Hws_tot l); intros [Hdr [Htrans [Hac Htot]]].
destruct (eqEv_dec x y) as [Hxyeq | Hdiff].
    rewrite <- Hxyeq in Htc; unfold util.acyclic in Hvalid; generalize (Hvalid x); intro Hc.
    contradiction.
  generalize (Htot x y Hdiff Hmx Hmy); intro Horxy.
  inversion Horxy as [Hxy | Hyx].
    destruct Hxy as [Hxy ?]; apply Hxy.
    destruct Hyx as [Hyx ?].
    assert (util.tc (ghb E X) x x) as Hxx.
      apply util.trc_ind with y; [apply Htc | apply util.trc_step; apply ws_in_ghb; apply Hyx].
unfold util.acyclic in Hvalid; generalize (Hvalid x); intro Hc.
contradiction.
Qed. *)

Lemma po_union_com_in_evts :
  forall E X,
  (well_formed_event_structure E) ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  Included _
    (Union _ (util.dom (util.rel_union (po_iico E) (com E X)))
       (util.ran (util.rel_union (po_iico E) (com E X)))) (events E).
Proof.
unfold Included; unfold util.domain; unfold util.range; unfold In;
intros E X Hwf Hvalid x Hx.
inversion Hx as [e Hdom | e Hran]; 
  [unfold In in Hdom; destruct Hdom as [x0 Hdom] | 
   unfold In in Hran; destruct Hran as [x0 Hran]].
  (*dom*)
  inversion Hdom as [Hpo | Hhb].
    (*po_iico*)
    change (events E x) with (In _ (events E) x); 
    eapply po_iico_domain_in_events; [apply Hwf | apply Hpo].
    (*hb*)
    change (events E x) with (In _ (events E) x); 
    eapply com_dom_in_evts; [apply Hwf | apply Hvalid | apply Hhb].
  (*ran*)
  inversion Hran as [Hpo | Hhb].
    (*po_iico*)
    change (events E x) with (In _ (events E) x); 
    eapply po_iico_range_in_events; [apply Hwf | apply Hpo].
    (*hb*)
    change (events E x) with (In _ (events E) x); 
    eapply com_ran_in_evts; [apply Hwf | apply Hvalid | apply Hhb].
Qed.

Lemma dom_ran_so_incl_po_com :
  forall E X,
  (well_formed_event_structure E) ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  Included _ (Union _ (util.dom (util.rel_union (po_iico E) (com E X)))
       (util.ran (util.rel_union (po_iico E) (com E X)))) (events E).
Proof.
intros E X Hwf Hvalid;
apply po_union_com_in_evts; auto.
Qed.

End DomRan.

Section Hexa.
Import util.
(*Definition com' (E:Event_struct) (X:Execution_witness) : util.Rln Event :=
  fun e1 => fun e2 => (rel_union (rel_union (com E X) (rel_seq (ws X) (rf X))) (rel_seq (fr E X) (rf X))) e1 e2.*)
Definition maybe_po (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 => (po_iico E) e1 e2 \/ e1 = e2.
Definition maybe_com' (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => (com' E X) e1 e2 \/ e1 = e2.

Definition pre_hexa (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => (tc (rel_seq (com' E X) (po_iico E))) e1 e2 \/ e1 = e2.

Definition hexa (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => 
    rel_seq (maybe_po E) (rel_seq (pre_hexa E X) (maybe_com' E X)) e1 e2. 

Definition pb (E:Event_struct) : Rln Event := po_iico E.

Lemma pb_in_com_po :
  forall E X,
  rel_incl (pb E) (tc (rel_union (com E X) (po_iico E))).
Proof.
unfold Included; unfold In; unfold pb;
intros E X x e Hpb.
apply trc_step; right; auto.
Qed.

(*Lemma ab_in_ghb :
  forall E X,
  rel_incl (abc E X) (ghb E X).
Proof.
unfold rel_incl;
intros E X x y Hab.
case_eq inter; case_eq intra; unfold ghb;
intros Hintra Hinter; rewrite Hintra; rewrite Hinter.
(*true,true*)
right; right; left; apply Hab.
(*true,false*)
right; left; apply Hab.
(*false,true*)
right; left; apply Hab.
(*false,false*)
left; apply Hab.
Qed.*)

(*Lemma ws_u_fr_in_ghb :
  forall E X,
  valid_execution E X ->
  rel_incl (rel_union (ws X) (fr E X)) (ghb E X).
Proof.
unfold rel_incl;
intros E X Hvalid x y Hab.
case_eq inter; case_eq intra; unfold ghb;
intros Hintra Hinter; rewrite Hintra; rewrite Hinter.
(*true,true*)
right; right; right; left; apply Hab.
(*true,false*)
right; right; left; apply Hab.
(*false,true*)
right; right; left; apply Hab.
(*false,false*)
right; left; apply Hab.
Qed. *)

Lemma com_ac :
  forall E X x, 
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(com E X x x).
Proof.
unfold not;
intros E X x [Hwswf Hrfwf] Hhb.
    destruct Hrfwf as [? [Hrf_cands ?]].
inversion Hhb as [Hrf_fr | Hws].
  inversion Hrf_fr as [Hrf | Hfr].
    (*rf*)
    generalize (Hrf_cands x x Hrf); intro Hrfc.
    destruct Hrfc as [Hex [Heex [l [Hwx Hrx]]]].
      case_eq (action x).
      intros dx lx vx Hx; case_eq dx; intro Hdx; rewrite Hdx in Hx;
         unfold write_to in Hwx; unfold read_from in Hrx;
         rewrite Hx in Hwx; rewrite Hx in Hrx.
           destruct Hwx as [v1 Hwx];
           inversion Hwx.
           destruct Hrx as [[v1 Hrx] ?];
           inversion Hrx.
    (*fr*)
    destruct Hfr as [Hex [Heex [wr [Hrf Hws]]]].
    generalize (Hrf_cands wr x Hrf); intro Hrfc.
    destruct Hrfc as [Hewr [Heeex [l [Hwwr Hrx]]]].
      case_eq (action x).
      intros dx lx vx Hx; case_eq dx; intro Hdx; rewrite Hdx in Hx;
         unfold read_from in Hrx; rewrite Hx in Hrx.
         generalize (ws_cands E X wr x Hwswf Hws); intro Hw.
           destruct Hw as [lwr [Hw_wr Hw_x]].
           destruct Hw_x as [Hudr Hwt_x].
           unfold write_to in Hwt_x; rewrite Hx in Hwt_x.
           destruct Hwt_x as [v1 Hwt_x];
           inversion Hwt_x.      
           destruct Hrx as [[v1 Hrx] ?];
           inversion Hrx.
  (*ws*)
    destruct Hwswf as [Hws_tot Hws_cands].
  generalize (ws_cy E X x Hws_tot Hws_cands); intro Hc; contradiction.
Qed. 

Lemma com_seq_com_implies_com' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X x y ->
  com E X y z ->
  com' E X x z.
Proof.
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.
inversion Hxy as [Hrf_fr_xy | Hws_xy];
inversion Hyz as [Hrf_fr_yz | Hws_yz].
  inversion Hrf_fr_xy as [Hrf_xy | Hfr_xy];
  inversion Hrf_fr_yz as [Hrf_yz | Hfr_yz].
    destruct_rf Hrfwf.
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    generalize (fr_ax1 Hfr_yz); intros [wr [Hrf Hws]].
    generalize (rf_uni X y x wr Hrfwf Hrf_xy Hrf); intro Heq.
    rewrite <- Heq in Hws; left; left; right; apply Hws.
    right; exists y; split; auto.
    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  
  inversion Hrf_fr_xy as [Hrf_xy | Hfr_xy].
    destruct_rf Hrfwf.
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.   
    destruct Hfr_xy as [? [? [wr [Hrf Hws]]]].
    generalize (ws_trans E X wr y z Hwswf Hws Hws_yz); intro Hws_wrz.
    left; left; left; right.
    eapply fr_ax2; [apply Hwf | | exists wr; split; auto]; split; auto.
  inversion Hrf_fr_yz as [Hrf_yz | Hfr_yz].
    left; right; exists y; split; auto.
    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  
    left; left; right;
    apply (ws_trans E X x y z Hwswf Hws_xy Hws_yz).
Qed.

Lemma com_seq_ws_rf_implies_com' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X x y ->
  rel_seq (ws X) (rf X) y z ->
  com' E X x z.
Proof.
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.
inversion Hxy as [Hrf_fr_xy | Hws_xy].
  inversion Hrf_fr_xy as [Hrf_xy | Hfr_xy].
    destruct Hyz as [? [Hws Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x0 Hwswf Hws); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.  
      destruct Hyz as [wz [Hws_ywz Hrfwz]].
      destruct Hfr_xy as [? [? [wx [Hrf_wx Hws_wxy]]]].
      generalize (ws_trans E X wx y wz Hwswf Hws_wxy Hws_ywz); intro Hws_wxwz.
      right; exists wz; split; [|apply Hrfwz].
      eapply fr_ax2; 
        [apply Hwf | | exists wx; split; [apply Hrf_wx | apply Hws_wxwz]]; split; auto.
      destruct Hyz as [wz [Hws_ywz Hrfwz]].
      generalize (ws_trans E X x y wz Hwswf Hws_xy Hws_ywz); intro Hws_xwz.
      left; right; exists wz; split; auto.
Qed.

Lemma com_seq_fr_rf_implies_com' :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X x y ->
  rel_seq (fr E X) (rf X) y z ->
  com' E X x z.
Proof.
intros E X x y z Hs Hxy Hyz.
generalize Hs; intros [Hwswf Hrfwf].
inversion Hxy as [Hrf_fr_xy | Hws_xy].
  inversion Hrf_fr_xy as [Hrf_xy | Hfr_xy].
    destruct Hyz as [wz [Hfr Hrf]].
    destruct Hfr as [? [? [wy [Hrf_y Hws_z]]]].
    generalize (rf_uni X y x wy Hrfwf Hrf_xy Hrf_y); intro Heq.
    rewrite <- Heq in Hws_z.
    left; right; exists wz; split; auto.
    destruct Hyz as [? [Hfr Hrf]].
    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.     
    destruct Hyz as [? [Hfr Hrf]].
    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.
Qed.

Lemma com_seq_com'_implies_com' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X x y ->
  com' E X y z ->
  com' E X x z.
Proof.
intros E X x y z Hwf Hvalid Hxy Hyz.
inversion Hyz as [Hhb_wsrf | Hfrrf].
  inversion Hhb_wsrf as [Hhb | Hwsrf].
    eapply com_seq_com_implies_com'; [apply Hwf | apply Hvalid | apply Hxy | apply Hhb].
    eapply com_seq_ws_rf_implies_com'; [apply Hwf | apply Hvalid | apply Hxy | apply Hwsrf].
    eapply com_seq_fr_rf_implies_com'; [apply Hvalid | apply Hxy | apply Hfrrf].
Qed.

Lemma ws_rf_seq_com_implies_com' :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (ws X) (rf X) x y ->
  com E X y z ->
  com' E X x z.
Proof.
intros E X x y z [Hwswf Hrfwf] Hxy Hyz.
inversion Hyz as [Hrf_fr_yz | Hws_yz].
  inversion Hrf_fr_yz as [Hrf_yz | Hfr_yz].
    destruct Hxy as [? [Hws Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.   
      destruct Hxy as [wy1 [Hws_xwy1 Hrf_wy1]].
      generalize (fr_ax1 Hfr_yz); intros [wy2 [Hrf_y2 Hws_z]].
      generalize (rf_uni X y wy1 wy2 Hrfwf Hrf_wy1 Hrf_y2); intro Heq.
        rewrite <- Heq in Hws_z.
        left; left; right; eapply ws_trans; [apply Hwswf | apply Hws_xwy1 | apply Hws_z].
    destruct Hxy as [? [Hws Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.     
Qed.

Lemma ws_rf_seq_com'_implies_com' :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (ws X) (rf X) x y ->
  com' E X y z ->
  com' E X x z.
Proof.
intros E X x y z Hvalid Hxy Hyz.
generalize Hvalid; intros [Hwswf Hrfwf].
inversion Hyz as [Hhb_wsrf_yz | Hfrrf_yz].
  inversion Hhb_wsrf_yz as [Hhb_yz | Hwsrf_yz].
    eapply ws_rf_seq_com_implies_com'; [apply Hvalid | apply Hxy | apply Hhb_yz].
    destruct Hxy as [? [Hws_x Hrf_y]].
    destruct Hwsrf_yz as [? [Hws_y Hrf_z]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [? [? Hry]].
    generalize (dom_ws_is_write E X y x1 Hwswf Hws_y); intros [? [? Hwy]].
    rewrite Hwy in Hry; inversion Hry.     
    destruct Hxy as [? [Hws_x Hrf_y]].
    destruct Hfrrf_yz as [? [Hfr_y Hrf_z]].
    destruct Hfr_y as [? [? [wy [Hrf_y2 Hws_z]]]].
    generalize (rf_uni X y x0 wy Hrfwf Hrf_y Hrf_y2); intro Heq.
    rewrite <- Heq in Hws_z.
    generalize (ws_trans E X x x0 x1 Hwswf Hws_x Hws_z); intro Hws_xx1.
    left; right; exists x1; split; auto.
Qed.

Lemma fr_rf_seq_com_implies_com' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (fr E X) (rf X) x y ->
  com E X y z ->
  com' E X x z.
Proof.
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.
inversion Hyz as [Hrf_fr_yz | Hws_yz].
  inversion Hrf_fr_yz as [Hrf_yz | Hfr_yz].
    destruct Hxy as [? [Hfr Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hxy as [? [Hfr Hrf]].
    destruct Hfr as [? [? [wx [Hrf_x Hws_wx]]]].
    destruct Hfr_yz as [? [? [wy [Hrf_y Hws_wyz]]]].
    generalize (rf_uni X y x0 wy Hrfwf Hrf Hrf_y); intro Heq.
    rewrite <- Heq in Hws_wyz.
    generalize (ws_trans E X wx x0 z Hwswf Hws_wx Hws_wyz); intro Hws_wxz.
    left; left; left; right; eapply fr_ax2; [apply Hwf | | exists wx; split; [apply Hrf_x | apply Hws_wxz]].
      split; auto.
    destruct Hxy as [? [Hfr Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
Qed.

Lemma com'_trans :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com' E X x y ->
  com' E X y z ->
  com' E X x z.
Proof.
intros E X x y z Hwf Ha Hxy Hyz.
inversion Hxy as [Hpxy | Hfrrf_xy];
inversion Hyz as [Hpyz | Hfrrf_yz].
  inversion Hpxy as [Hhb_xy | Hwsfr_xy];
  inversion Hpyz as [Hhb_yz | Hwsfr_yz].
    eapply com_seq_com_implies_com'; [apply Hwf | apply Ha | apply Hhb_xy | apply Hhb_yz].
    eapply com_seq_ws_rf_implies_com'; [apply Hwf | apply Ha | apply Hhb_xy | apply Hwsfr_yz].
    eapply ws_rf_seq_com_implies_com'; [apply Ha | apply Hwsfr_xy | apply Hhb_yz].
    destruct Hwsfr_xy as [? [Hws_x Hrf_y]];
    destruct Hwsfr_yz as [? [Hws_y Hrf_z]].
    destruct Ha as [Hwswf Hrfwf].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x1 Hwswf Hws_y); intros [? [? Hwy]].
    rewrite Hwy in Hry; inversion Hry.
  inversion Hpxy as [Hhb_xy | Hwsfr_xy].
    eapply com_seq_fr_rf_implies_com'; [apply Ha | apply Hhb_xy | apply Hfrrf_yz].
    destruct Hfrrf_yz as [wz [Hfr_y Hrf_z]];
    destruct Hwsfr_xy as [wy1 [Hws_x Hrf_y1]].
     destruct Hfr_y as [? [? [wy2 [Hrf_y2 Hws_wz]]]].
    destruct Ha as [Hwswf Hrfwf].
     generalize (rf_uni X y wy1 wy2 Hrfwf Hrf_y1 Hrf_y2); intro Heq.
     rewrite <-  Heq in Hws_wz.
     generalize (ws_trans E X x wy1 wz Hwswf Hws_x Hws_wz); intro Hws_xwz.
     left; right; exists wz; split; auto.
  inversion Hpyz as [Hhb_yz | Hwsfr_yz].
    eapply fr_rf_seq_com_implies_com'; [apply Hwf | apply Ha | apply Hfrrf_xy | apply Hhb_yz].
    destruct Hfrrf_xy as [? [Hfr_x Hrf_y]].
    destruct Hwsfr_yz as [? [Hws_y Hrf_z]].
    destruct Ha as [Hwswf Hrfwf].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x1 Hwswf Hws_y); intros [? [? Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hfrrf_xy as [wy1 [Hfr_x Hrf_y]];
    destruct Hfrrf_yz as [wz [Hfr_y Hrf_z]].
     destruct Hfr_y as [? [? [wy2 [Hrf_y2 Hws_wz]]]].
     destruct Hfr_x as [? [? [wx [Hrf_x Hws_x]]]].
    generalize Ha; intros [Hwswf Hrfwf].
     generalize (rf_uni X y wy1 wy2 Hrfwf Hrf_y Hrf_y2); intro Heq.
     rewrite <- Heq in Hws_wz.
     generalize (ws_trans E X wx wy1 wz Hwswf Hws_x Hws_wz); intro Hws_wxwz.
    assert (exists wr : Event, rf X wr x /\ ws X wr wz) as Hfrax_xwz.
      exists wx; split; auto.
     generalize (fr_ax2 X x wz Hwf Ha Hfrax_xwz); intro Hfr_xwz.
     right; exists wz; split; auto.
Qed.

Lemma pre_hexa_rel_seq_left :
  forall E X x y z,
  pre_hexa E X x y ->
  rel_seq (com' E X) (po_iico E) y z ->
  pre_hexa E X x z.
Proof.
intros E X x y z Hhx_xy Hseq_yz.
inversion Hhx_xy as [Htc_xy | Heq_xy].
  left; apply trc_ind with y; [apply Htc_xy | apply trc_step; apply Hseq_yz].
  subst; left; apply trc_step; apply Hseq_yz.
Qed.

Lemma pre_hexa_trans :
  forall E X x y z,
  pre_hexa E X x y ->
  pre_hexa E X y z ->
  pre_hexa E X x z.
Proof.
intros E X x y z Hxy Hyz.
inversion Hxy as [Htc_xy | Heq_xy];
inversion Hyz as [Htc_yz | Heq_yz].
  left; apply trc_ind with y; auto.
  left; subst; auto.
  left; subst; auto.
  right; subst; auto.
Qed.

Lemma hexa_trans : 
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  hexa E X x z -> hexa E X z y ->
  hexa E X x y.
Proof.
intros E X x y z Hwf Hvalid Hxz Hzy.
assert (trans (com' E X)) as Htr_hb'.
  unfold trans; intros e1 e2 e3 H12 H23.
eapply com'_trans; [apply Hwf | apply Hvalid | apply H12 | apply H23].
assert (trans (po_iico E)) as Htr_po.
  unfold trans; intros e1 e2 e3 H12 H23.
eapply po_trans; [apply Hwf | apply H12 | apply H23].
generalize (hx_trans Htr_hb' Htr_po); intro Htr_hx.
  unfold util.trans in Htr_hx; unfold hx in Htr_hx; unfold phx in Htr_hx.
unfold hexa in * |- *.
  apply (Htr_hx x z y Hxz Hzy).
Qed.

Lemma hx_hexa :
  forall E X,
  hexa E X = hx (com' E X) (po_iico E).
Proof.
intros E X.
unfold hexa; unfold hx; unfold maybe_po; unfold phx;
  unfold pre_hexa; unfold maybe_com'; unfold maybe; auto.
Qed.

Lemma com_po_implies_hexa_path : (*1*)
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (tc (rel_union (com E X) (po_iico E)) x y)->
  (hexa E X) x y.
Proof.
intros E X x y Hwf Hvalid Hin.
rewrite (hx_hexa E X).
eapply union_implies_hexa_path.
unfold trans; intros x1 x2 x3 H12 H23; apply com'_trans with x2; auto.
unfold trans; intros x1 x2 x3 H12 H23; apply po_trans with x2; auto.
intros e1 e2 H12; left; left; apply H12.
exact Hin.
Qed.

Lemma ac_u :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, rel_union (com E X) (po_iico E) x x).
unfold not;
intros E X Hwf Hs [x Hx].
inversion Hx as [Hhb | Hpo].
  generalize (com_ac Hs Hhb); trivial.
  generalize (po_ac Hwf Hpo); trivial.
Qed.

Lemma com'_ac :
  forall E X x,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(com' E X x x).
Proof.
unfold not;
intros E X x Hs Hx.
inversion Hx as [Hpx | Hfrrf].
  inversion Hpx as [Hhb | Hwsrf].
    generalize Hhb; fold (~(com E X x x)); eapply com_ac.
      auto.
    destruct Hwsrf as [? [Hws Hrf]].
    destruct Hs as [Hwswf [? [Hrf_cands ?]]].
    generalize (ran_rf_is_read E X x0 x Hrf_cands Hrf); intros [? [? Hrx]].
    generalize (dom_ws_is_write E X x x0 Hwswf Hws); intros [? [? Hwx]].
    rewrite Hwx in Hrx; inversion Hrx.
    destruct Hfrrf as [wx1 [Hfr Hrf1]].
    destruct Hfr as [? [? [wx2 [Hrf2 Hws]]]].
    destruct Hs as [Hwswf Hrfwf].    
    generalize (rf_uni X x wx1 wx2 Hrfwf Hrf1 Hrf2); intro Heq; subst.
    destruct Hwswf as [Hws_tot Hws_cands].
    generalize (ws_cy E X wx2 Hws_tot Hws_cands); intro Hc.
    contradiction.
Qed.

Lemma com_hexa :
  forall E X x z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X x z ->
  hexa E X z x ->
  exists y : Event, tc (rel_seq (com' E X) (po_iico E)) y y.
Proof.
intros E X x z Hwf Hvalid Hhb_xz Hhx_zx.
eapply r1_hexa.
unfold not; intros [e Hhb]. 
generalize (com'_ac); intro thm; unfold not in thm; apply (thm E X e Hvalid Hhb).
intros e1 e2 H12; left; left; apply H12.
unfold trans; intros; eapply com'_trans; auto.
  apply H. apply H0.
unfold trans; intros; eapply po_trans; auto.
  apply H. apply H0.
apply Hhb_xz.
rewrite <- hx_hexa; auto.
Qed.

Lemma hexa_po :
  forall E X x z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  hexa E X x z ->
  (po_iico E) z x ->
  exists y : Event, tc (rel_seq (com' E X) (po_iico E)) y y.
Proof.
intros E X x z Hwf Hvalid Hhx_xz Hpo_zx.
eapply hexa_r.
unfold not; intros [e Hpo]. 
generalize (po_ac); intro thm; unfold not in thm; apply (thm E e Hwf Hpo).
unfold trans; intros; eapply po_trans; auto.
  apply H. apply H0.
rewrite <- hx_hexa; auto.
apply Hhx_xz.
apply Hpo_zx.
Qed.

Lemma com_union_po_cycle_implies_com'_seq_po_cycle : (*2*)
  forall E X x,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (tc (rel_union (com E X) (po_iico E))) x x ->
  (exists y, (tc (rel_seq (com' E X) (po_iico E))) y y).
Proof.
intros E X x Hwf Hvalid Hc.
eapply union_cycle_implies_seq_cycle.
apply (ac_u Hwf Hvalid).
unfold not; intros [e Hpo]. 
generalize (po_ac); intro thm; unfold not in thm; apply (thm E e Hwf Hpo).
unfold not; intros [e Hhb]. 
generalize (com'_ac); intro thm; unfold not in thm; apply (thm E X e Hvalid Hhb).
unfold trans; intros; eapply com'_trans; auto.
  apply H. apply H0.
unfold trans; intros; eapply po_trans; auto.
  apply H. apply H0.
left; left; auto.
apply Hc.
Qed.

Lemma ppo_ac :
  forall E x, 
  well_formed_event_structure E ->
  ~((ppo E) x x).
Proof.
unfold not;
intros E x Hwf Hppo.
unfold well_formed_event_structure in Hwf.
generalize (ppo_valid E x x Hppo); intro Hpo_iico.
apply (po_ac Hwf Hpo_iico).
Qed.

Lemma ac_u_ppo :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, rel_union (com E X) (ppo E) x x).
unfold not;
intros E X Hwf Hvalid [x Hx].
inversion Hx as [Hhb | Hpo].
  generalize (com_ac Hvalid Hhb); trivial.
  generalize (ppo_ac Hwf Hpo); trivial.
Qed.

(*Lemma mhb_in_hb :
  forall E X,
  rel_incl (mhb E X) (hb E X).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra;
unfold mhb; rewrite Hinter; rewrite Hintra; intros E X x y Hxy.

inversion Hxy as [Hrfe | Hr].
  left; left; destruct Hrfe; auto.
  inversion Hr as [Hrfi | Hu].
    left; left; destruct Hrfi; auto.
    inversion Hu as [Hws | Hfr].
      right; auto. left; right; auto.

  inversion Hxy as [Hrfe | Hu].
    left; left; destruct Hrfe; auto.
    inversion Hu as [Hws | Hfr].
      right; auto. left; right; auto.

  inversion Hxy as [Hrfi | Hu].
    left; left; destruct Hrfi; auto.
    inversion Hu as [Hws | Hfr].
      right; auto. left; right; auto.

    inversion Hxy as [Hws | Hfr].
      right; auto. left; right; auto.
Qed.

Lemma mhb_ac :
  forall E X x,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(mhb E X x x).
Proof.
unfold not;
intros E X x Hs Hx.
generalize (mhb_in_hb E X x x Hx); intro Hhb.
apply (hb_ac Hs Hhb).
Qed.

Lemma ac_mhb_u_ppo :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, rel_union (mhb E X) (ppo E) x x).
unfold not;
intros E X Hwf Hs [x Hx].
inversion Hx as [Hhb | Hpo].
  generalize (mhb_ac X x Hs Hhb); trivial.
  generalize (ppo_ac Hwf Hpo); trivial.
Qed.

Lemma mhb_seq_mhb_implies_mhb' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  mhb E X x y ->
  mhb E X y z ->
  mhb' E X x z.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mhb; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra;
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.

inversion Hxy as [Hrfe_xy | Hr_xy];
inversion Hyz as [Hrfe_yz | Hr_yz].

  destruct_rf Hrfwf.
  destruct Hrfe_xy as [Hrf_xy ?]; destruct Hrfe_yz as [Hrf_yz ?].
  generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
  generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
  rewrite Hwy in Hry; inversion Hry.

  inversion Hr_yz as [Hrfi_yz | Hws_fr_yz].
  
    destruct_rf Hrfwf.
    destruct Hrfe_xy as [Hrf_xy ?]; destruct Hrfi_yz as [Hrf_yz ?].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
  
    inversion Hws_fr_yz as [Hws_yz | Hfr_yz].
      destruct_rf Hrfwf.
      destruct Hrfe_xy as [Hrf_xy ?].
      generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
      generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
      rewrite Hwy in Hry; inversion Hry.   
      generalize (fr_ax1 Hfr_yz); intros [wr [Hrf Hws]].
      destruct Hrfe_xy as [Hrf_xy ?].
      generalize (rf_uni X y x wr Hrfwf Hrf_xy Hrf); intro Heq.
      rewrite <- Heq in Hws; left; left; right; right; left; apply Hws.

  inversion Hr_xy as [Hrfi_xy | Hws_fr_xy].

    destruct_rf Hrfwf.
    destruct Hrfi_xy as [Hrf_xy ?]; destruct Hrfe_yz as [Hrf_yz ?].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

    inversion Hws_fr_xy as [Hws_xy | Hfr_xy].
      left; right; exists y; split; auto; right; auto.
      right; exists y; split; auto; right; auto.

  inversion Hr_xy as [Hrfi_xy | Hws_fr_xy]; inversion Hr_yz as [Hrfi_yz | Hws_fr_yz].
    destruct_rf Hrfwf.
    destruct Hrfi_xy as [Hrf_xy ?]; destruct Hrfi_yz as [Hrf_yz ?].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].    
    rewrite Hwy in Hry; inversion Hry.

    inversion Hws_fr_yz as [Hws_yz | Hfr_yz].
      destruct_rf Hrfwf.          
      destruct Hrfi_xy as [Hrf_xy ?].
      generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
      generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].    
      rewrite Hwy in Hry; inversion Hry.

      generalize (fr_ax1 Hfr_yz); intros [wr [Hrf Hws]].
      destruct Hrfi_xy as [Hrf_xy ?].
      generalize (rf_uni X y x wr Hrfwf Hrf_xy Hrf); intro Heq.
      rewrite <- Heq in Hws; left; left; right; right; left; apply Hws.

    inversion Hws_fr_xy as [Hws_xy | Hfr_xy].
      left; right; exists y; split; auto; left; auto.
      right; exists y; split; auto; left; auto.

    inversion Hws_fr_yz as [Hws_yz | Hfr_yz];  inversion Hws_fr_xy as [Hws_xy | Hfr_xy].
    left; left; right; right; left.
      apply (ws_trans E X x y z Hwswf Hws_xy Hws_yz).      

    destruct Hfr_xy as [? [? [wr [Hrf Hws]]]].
    generalize (ws_trans E X wr y z Hwswf Hws Hws_yz); intro Hws_wrz.
    left; left; right; right; right.
    eapply fr_ax2; [apply Hwf | | exists wr; split; auto]; split; auto.
    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

inversion Hxy as [Hrfe_xy | Hr_xy];
inversion Hyz as [Hrfe_yz | Hr_yz].  

  destruct_rf Hrfwf.
  destruct Hrfe_xy as [Hrf_xy ?]; destruct Hrfe_yz as [Hrf_yz ?].
  generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
  generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
  rewrite Hwy in Hry; inversion Hry.

  inversion Hr_yz as [Hws_yz | Hfr_yz].
  
      destruct_rf Hrfwf.
      destruct Hrfe_xy as [Hrf_xy ?].
      generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
      generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
      rewrite Hwy in Hry; inversion Hry.   
      generalize (fr_ax1 Hfr_yz); intros [wr [Hrf Hws]].
      destruct Hrfe_xy as [Hrf_xy ?].
      generalize (rf_uni X y x wr Hrfwf Hrf_xy Hrf); intro Heq.
      rewrite <- Heq in Hws; left; left; right; left ; apply Hws.

  inversion Hr_xy as [Hws_xy | Hfr_xy].

      left; right; exists y; split; auto; right; auto.
      right; exists y; split; auto; right; auto.

  inversion Hr_xy as [Hws_xy | Hfr_xy]; inversion Hr_yz as [Hws_yz | Hfr_yz].
    left; left; right; left.
      apply (ws_trans E X x y z Hwswf Hws_xy Hws_yz).      

    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  

    destruct Hfr_xy as [? [? [wr [Hrf Hws]]]].
    generalize (ws_trans E X wr y z Hwswf Hws Hws_yz); intro Hws_wrz.
    left; left; right; right.
    eapply fr_ax2; [apply Hwf | | exists wr; split; auto]; split; auto.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

inversion Hxy as [Hrfi_xy | Hr_xy];
inversion Hyz as [Hrfi_yz | Hr_yz].  

  destruct_rf Hrfwf.
  destruct Hrfi_xy as [Hrf_xy ?]; destruct Hrfi_yz as [Hrf_yz ?].
  generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
  generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
  rewrite Hwy in Hry; inversion Hry.

  inversion Hr_yz as [Hws_yz | Hfr_yz].
  
      destruct_rf Hrfwf.
      destruct Hrfi_xy as [Hrf_xy ?].
      generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
      generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
      rewrite Hwy in Hry; inversion Hry.   
      generalize (fr_ax1 Hfr_yz); intros [wr [Hrf Hws]].
      destruct Hrfi_xy as [Hrf_xy ?].
      generalize (rf_uni X y x wr Hrfwf Hrf_xy Hrf); intro Heq.
      rewrite <- Heq in Hws; left; left; right; left ; apply Hws.

  inversion Hr_xy as [Hws_xy | Hfr_xy].

      left; right; exists y; split; auto; left; auto.
      right; exists y; split; auto; left; auto.

  inversion Hr_xy as [Hws_xy | Hfr_xy]; inversion Hr_yz as [Hws_yz | Hfr_yz].
    left; left; right; left.
      apply (ws_trans E X x y z Hwswf Hws_xy Hws_yz).      

    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  

    destruct Hfr_xy as [? [? [wr [Hrf Hws]]]].
    generalize (ws_trans E X wr y z Hwswf Hws Hws_yz); intro Hws_wrz.
    left; left; right; right.
    eapply fr_ax2; [apply Hwf | | exists wr; split; auto]; split; auto.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

inversion Hxy as [Hws_xy | Hfr_xy];
inversion Hyz as [Hws_yz | Hfr_yz].  

    left; left; left;
      apply (ws_trans E X x y z Hwswf Hws_xy Hws_yz).      

    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  

    destruct Hfr_xy as [? [? [wr [Hrf Hws]]]].
    generalize (ws_trans E X wr y z Hwswf Hws Hws_yz); intro Hws_wrz.
    left; left; right.
    eapply fr_ax2; [apply Hwf | | exists wr; split; auto]; split; auto.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.
Qed.

Lemma mhb_seq_ws_rf_implies_mhb' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  mhb E X x y ->
  rel_seq (ws X) (mrf X) y z ->
  mhb' E X x z.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mhb; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra;
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.

inversion Hxy as [Hrfe_xy | Hr_xy]; destruct Hyz as [? [Hws Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    destruct Hrfe_xy as [Hrf_xy ?].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x0 Hwswf Hws); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.  

  inversion Hr_xy as [Hrfi_xy | Hws_fr_xy].
    destruct Hrfwf as [? [Hrf_cands ?]].
    destruct Hrfi_xy as [Hrf_xy ?].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x0 Hwswf Hws); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  inversion Hws_fr_xy as [Hws_xy | Hfr_xy].
    left; right; exists x0; split; auto.
    apply (ws_trans E X x y x0 Hwswf Hws_xy Hws).

  right; exists x0; split; auto.
      destruct Hfr_xy as [? [? [wx [Hrf_wx Hws_wxy]]]].
      eapply fr_ax2; 
        [apply Hwf | | exists wx; split; [apply Hrf_wx | ]]. auto.
        apply (ws_trans E X wx y x0 Hwswf Hws_wxy Hws).

inversion Hxy as [Hrfi_xy | Hr_xy]; destruct Hyz as [? [Hws Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    destruct Hrfi_xy as [Hrf_xy ?].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x0 Hwswf Hws); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.  

  inversion Hr_xy as [Hws_xy | Hfr_xy].
    left; right; exists x0; split; auto.
    apply (ws_trans E X x y x0 Hwswf Hws_xy Hws).

  right; exists x0; split; auto.
      destruct Hfr_xy as [? [? [wx [Hrf_wx Hws_wxy]]]].
      eapply fr_ax2; 
        [apply Hwf | | exists wx; split; [apply Hrf_wx | ]]. auto.
        apply (ws_trans E X wx y x0 Hwswf Hws_wxy Hws).

inversion Hxy as [Hrfi_xy | Hr_xy]; destruct Hyz as [? [Hws Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    destruct Hrfi_xy as [Hrf_xy ?].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x0 Hwswf Hws); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.  

  inversion Hr_xy as [Hws_xy | Hfr_xy].
    left; right; exists x0; split; auto.
    apply (ws_trans E X x y x0 Hwswf Hws_xy Hws).

  right; exists x0; split; auto.
      destruct Hfr_xy as [? [? [wx [Hrf_wx Hws_wxy]]]].
      eapply fr_ax2; 
        [apply Hwf | | exists wx; split; [apply Hrf_wx | ]]. auto.
        apply (ws_trans E X wx y x0 Hwswf Hws_wxy Hws).

  inversion Hxy as [Hws_xy | Hfr_xy]; destruct Hyz as [? [Hws Hrf]].
    left; right; exists x0; split; auto.
    apply (ws_trans E X x y x0 Hwswf Hws_xy Hws).

  right; exists x0; split; auto.
      destruct Hfr_xy as [? [? [wx [Hrf_wx Hws_wxy]]]].
      eapply fr_ax2; 
        [apply Hwf | | exists wx; split; [apply Hrf_wx | ]]. auto.
        apply (ws_trans E X wx y x0 Hwswf Hws_wxy Hws).
Qed.

Lemma mhb_seq_fr_mrf_implies_mhb' :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  mhb E X x y ->
  rel_seq (fr E X) (mrf X) y z ->
  mhb' E X x z.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mhb; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra;
intros E X x y z Hs Hxy Hyz;
generalize Hs; intros [Hwswf Hrfwf].

inversion Hxy as [Hrfe_xy | Hr_xy]; destruct Hyz as [? [Hfr Hrf]].
  
    destruct Hfr as [? [? [wy [Hrf_y Hws_z]]]].
    destruct Hrfe_xy as [Hrf_xy ?].
    generalize (rf_uni X y x wy Hrfwf Hrf_xy Hrf_y); intro Heq.
    rewrite <- Heq in Hws_z.
    left; right; exists x0; split; auto.

  inversion Hr_xy as [Hrfi_xy | Hws_fr_xy].

    destruct Hfr as [? [? [wy [Hrf_y Hws_z]]]].
    destruct Hrfi_xy as [Hrf_xy ?].
    generalize (rf_uni X y x wy Hrfwf Hrf_xy Hrf_y); intro Heq.
    rewrite <- Heq in Hws_z.
    left; right; exists x0; split; auto.

  inversion Hws_fr_xy as [Hws_xy | Hfr_xy].

    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.    

inversion Hxy as [Hrfe_xy | Hr_xy]; destruct Hyz as [? [Hfr Hrf]].
  
    destruct Hfr as [? [? [wy [Hrf_y Hws_z]]]].
    destruct Hrfe_xy as [Hrf_xy ?].
    generalize (rf_uni X y x wy Hrfwf Hrf_xy Hrf_y); intro Heq.
    rewrite <- Heq in Hws_z.
    left; right; exists x0; split; auto.

  inversion Hr_xy as [Hws_xy | Hfr_xy].

    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

inversion Hxy as [Hrfi_xy | Hr_xy]; destruct Hyz as [? [Hfr Hrf]].
  
    destruct Hfr as [? [? [wy [Hrf_y Hws_z]]]].
    destruct Hrfi_xy as [Hrf_xy ?].
    generalize (rf_uni X y x wy Hrfwf Hrf_xy Hrf_y); intro Heq.
    rewrite <- Heq in Hws_z.
    left; right; exists x0; split; auto.

  inversion Hr_xy as [Hws_xy | Hfr_xy].

    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry. 

inversion Hxy as [Hws_xy | Hfr_xy]; destruct Hyz as [? [Hfr Hrf]].
 
    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.
Qed.

Lemma mhb_seq_mhb'_implies_mhb' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  mhb E X x y ->
  mhb' E X y z ->
  mhb' E X x z.
Proof.
intros E X x y z Hwf Hvalid Hxy Hyz;
inversion Hyz as [Hmhb_wsrf | Hfrrf].
  inversion Hmhb_wsrf as [Hmhb | Hwsrf].
    eapply mhb_seq_mhb_implies_mhb'; [apply Hwf | apply Hvalid | apply Hxy | apply Hmhb].
    eapply mhb_seq_ws_rf_implies_mhb'; [apply Hwf | apply Hvalid | apply Hxy | apply Hwsrf].
    eapply mhb_seq_fr_mrf_implies_mhb'; [apply Hvalid | apply Hxy | apply Hfrrf].
Qed.

Lemma ws_mrf_seq_mhb_implies_mhb' :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (ws X) (mrf X) x y ->
  mhb E X y z ->
  mhb' E X x z.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mhb; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra;
intros E X x y z Hs Hxy Hyz;
generalize Hs; intros [Hwswf Hrfwf].

inversion Hyz as [Hrfe_yz | Hu_yz]; destruct Hxy as [? [Hws Hrf]].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?]; destruct Hrfe_yz as [Hrf_yz ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hrfe_y as [Hrf_y ?]; destruct Hrfe_yz as [Hrf_yz ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  inversion Hu_yz as [Hrfi_yz | Hws_fr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?]; destruct Hrfi_yz as [Hrf_yz ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hrfe_y as [Hrf_y ?]; destruct Hrfi_yz as [Hrf_yz ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  inversion Hws_fr_yz as [Hws_yz | Hfr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y];
      generalize (fr_ax1 Hfr_yz); intros [wy2 [Hrf_y2 Hws_z]].
        destruct Hrfi_y as [Hrf_y ?].
      generalize (rf_uni X y x0 wy2 Hrfwf Hrf_y Hrf_y2); intro Heq.
        rewrite <- Heq in Hws_z.
        left; left; right; right; left; eapply ws_trans; [apply Hwswf | apply Hws | apply Hws_z].
       destruct Hrfe_y as [Hrf_y ?].
      generalize (rf_uni X y x0 wy2 Hrfwf Hrf_y Hrf_y2); intro Heq.
        rewrite <- Heq in Hws_z.
        left; left; right; right; left; eapply ws_trans; [apply Hwswf | apply Hws | apply Hws_z].

inversion Hyz as [Hrfe_yz | Hu_yz]; destruct Hxy as [? [Hws Hrf]].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].

    inversion Hrfi_y.

    destruct Hrfe_y as [Hrf_y ?]; destruct Hrfe_yz as [Hrf_yz ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  inversion Hu_yz as [Hws_yz | Hfr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    inversion Hrfi_y.  
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y];
      generalize (fr_ax1 Hfr_yz); intros [wy2 [Hrf_y2 Hws_z]].
        inversion Hrfi_y.
       destruct Hrfe_y as [Hrf_y ?].
      generalize (rf_uni X y x0 wy2 Hrfwf Hrf_y Hrf_y2); intro Heq.
        rewrite <- Heq in Hws_z.
        left; left; right; left; eapply ws_trans; [apply Hwswf | apply Hws | apply Hws_z].

inversion Hyz as [Hrfi_yz | Hu_yz]; destruct Hxy as [? [Hws Hrf]].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].

    destruct Hrfi_y as [Hrf_y ?]; destruct Hrfi_yz as [Hrf_yz ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

    inversion Hrfe_y.

  inversion Hu_yz as [Hws_yz | Hfr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    inversion Hrfe_y.  

  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y];
      generalize (fr_ax1 Hfr_yz); intros [wy2 [Hrf_y2 Hws_z]].
       destruct Hrfi_y as [Hrf_y ?].
      generalize (rf_uni X y x0 wy2 Hrfwf Hrf_y Hrf_y2); intro Heq.
        rewrite <- Heq in Hws_z.
        left; left; right; left; eapply ws_trans; [apply Hwswf | apply Hws | apply Hws_z].
        inversion Hrfe_y.

inversion Hyz as [Hws_yz | Hfr_yz]; destruct Hxy as [? [Hws Hrf]].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    inversion Hrfi_y.  
    inversion Hrfe_y.  

  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    inversion Hrfi_y.  
    inversion Hrfe_y. 
Qed.

Lemma ws_rf_seq_mhb'_implies_mhb' :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (ws X) (mrf X) x y ->
  mhb' E X y z ->
  mhb' E X x z.
Proof.
intros E X x y z Hvalid Hxy Hyz.
generalize Hvalid; intros [Hwswf Hrfwf].
inversion Hyz as [Hhb_wsrf_yz | Hfrrf_yz].
  inversion Hhb_wsrf_yz as [Hhb_yz | Hwsrf_yz].
    eapply ws_mrf_seq_mhb_implies_mhb'; [apply Hvalid | apply Hxy | apply Hhb_yz].
    destruct Hxy as [? [Hws_x Hrf_y]].
    destruct Hwsrf_yz as [? [Hws_y Hrf_z]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_mrf_is_read E Hrf_cands Hrf_y); intros [? [? Hry]]. 
       generalize (dom_ws_is_write E X y x1 Hwswf Hws_y); intros [? [? Hwy]]. 
    rewrite Hwy in Hry; inversion Hry.  
    destruct Hxy as [? [Hws_x Hrf_y]].
    destruct Hfrrf_yz as [? [Hfr_y Hrf_z]].
    destruct Hfr_y as [? [? [wy [Hrf_y2 Hws_z]]]].
    generalize (mrf_rf_uni wy Hrfwf Hrf_y Hrf_y2); intro Heq.
    rewrite <- Heq in Hws_z.
    generalize (ws_trans E X x x0 x1 Hwswf Hws_x Hws_z); intro Hws_xx1.
    left; right; exists x1; split; auto.
Qed.

Lemma fr_mrf_seq_mhb_implies_mhb' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (fr E X) (mrf X) x y ->
  mhb E X y z ->
  mhb' E X x z.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mhb; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra;
intros E X x y z Hwf Hs Hxy Hyz;
generalize Hs; intros [Hwswf Hrfwf].

inversion Hyz as [Hrfe_yz | Hu_yz]; destruct Hxy as [? [Hfr Hrf]].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y]; destruct Hrfe_yz as [Hrf_yz ?].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  inversion Hu_yz as [Hrfi_yz | Hws_fr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y]; destruct Hrfi_yz as [Hrf_yz ?].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  inversion Hws_fr_yz as [Hws_yz | Hfr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hfr_yz as [? [? [wy [Hrf_yw Hws_wyz]]]].
    destruct Hfr as [? [? [wx [Hrf_x Hws_wx]]]].
    generalize (rf_uni X y x0 wy Hrfwf Hrf_y Hrf_yw); intro Heq.
    rewrite <- Heq in Hws_wyz.
    generalize (ws_trans E X wx x0 z Hwswf Hws_wx Hws_wyz); intro Hws_wxz.
    left; left; right; right; right; eapply fr_ax2; [apply Hwf | | exists wx; split; [apply Hrf_x | apply Hws_wxz]].
      split; auto.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hfr_yz as [? [? [wy [Hrf_yw Hws_wyz]]]].
    destruct Hfr as [? [? [wx [Hrf_x Hws_wx]]]].
    generalize (rf_uni X y x0 wy Hrfwf Hrf_y Hrf_yw); intro Heq.
    rewrite <- Heq in Hws_wyz.
    generalize (ws_trans E X wx x0 z Hwswf Hws_wx Hws_wyz); intro Hws_wxz.
    left; left; right; right; right; eapply fr_ax2; [apply Hwf | | exists wx; split; [apply Hrf_x | apply Hws_wxz]].
      split; auto.

inversion Hyz as [Hrfe_yz | Hu_yz]; destruct Hxy as [? [Hfr Hrf]].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y]; destruct Hrfe_yz as [Hrf_yz ?].
    inversion Hrfi_y.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

  inversion Hu_yz as [Hws_yz | Hfr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    inversion Hrfi_y.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    inversion Hrfi_y.
    destruct Hrfe_y as [Hrf_y ?].
    destruct Hfr_yz as [? [? [wy [Hrf_yw Hws_wyz]]]].
    destruct Hfr as [? [? [wx [Hrf_x Hws_wx]]]].
    generalize (rf_uni X y x0 wy Hrfwf Hrf_y Hrf_yw); intro Heq.
    rewrite <- Heq in Hws_wyz.
    generalize (ws_trans E X wx x0 z Hwswf Hws_wx Hws_wyz); intro Hws_wxz.
    left; left; right; right; eapply fr_ax2; [apply Hwf | | exists wx; split; [apply Hrf_x | apply Hws_wxz]].
      split; auto.

inversion Hyz as [Hrfi_yz | Hu_yz]; destruct Hxy as [? [Hfr Hrf]].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y]; destruct Hrfi_yz as [Hrf_yz ?].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    inversion Hrfe_y.

  inversion Hu_yz as [Hws_yz | Hfr_yz].
  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    inversion Hrfe_y.

  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    destruct Hrfi_y as [Hrf_y ?].
    destruct Hfr_yz as [? [? [wy [Hrf_yw Hws_wyz]]]].
    destruct Hfr as [? [? [wx [Hrf_x Hws_wx]]]].
    generalize (rf_uni X y x0 wy Hrfwf Hrf_y Hrf_yw); intro Heq.
    rewrite <- Heq in Hws_wyz.
    generalize (ws_trans E X wx x0 z Hwswf Hws_wx Hws_wyz); intro Hws_wxz.
    left; left; right; right; eapply fr_ax2; [apply Hwf | | exists wx; split; [apply Hrf_x | apply Hws_wxz]].
      split; auto.
    inversion Hrfe_y.

inversion Hyz as [Hws_yz | Hfr_yz]; destruct Hxy as [? [Hfr Hrf]].

  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    inversion Hrfi_y.
    inversion Hrfe_y.

  simpl in Hrf; inversion Hrf as [Hrfi_y | Hrfe_y].
    inversion Hrfi_y.
    inversion Hrfe_y.
Qed.

Lemma mhb'_dec :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  mhb' E X x y ->  
  mhb E X x y \/ rel_seq (ws X) (mrf X) x y \/  rel_seq (fr E X) (mrf X) x y.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra; intros E X x y Hwf Hs Hxy.
  inversion Hxy as [Hu | Hfrs];
    [inversion Hu as [Hmhb | Hwss];
       [left; auto | right; left; auto] |
       right; auto].
  inversion Hxy as [Hu | Hfrs];
    [inversion Hu as [Hmhb | Hwss];
       [left; auto | right; left; auto] |
       right; auto].
  inversion Hxy as [Hu | Hfrs];
    [inversion Hu as [Hmhb | Hwss];
       [left; auto | right; left; auto] |
       right; auto].
  inversion Hxy as [Hu | Hfrs];
    [inversion Hu as [Hmhb | Hwss];
       [left; auto | right; left; auto] |
       right; auto].
Qed.

Lemma ws_mrf_fr_mrf_implies_mhb' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (ws X) (mrf X) x y ->
  rel_seq (fr E X) (mrf X) y z ->
  mhb' E X x z.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra; simpl; intros E X x y z Hwf Hs Hxy Hyz;
generalize Hs; intros [Hwswf Hrfwf];
destruct Hxy as [w1 [Hws1 Hmrf1]]; destruct Hyz as [w2 [[Hey [Hez [wy [Hrf Hws2]]]] Hmrf2]].

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    destruct Hmrfi1 as [Hrf1 ?].
    generalize (rf_uni X y wy w1 Hrfwf Hrf Hrf1); intro Heq.
    rewrite Heq in Hws2; generalize (ws_trans E X x w1 w2 Hwswf Hws1 Hws2); intro Hws.
    left; right; exists w2; split; auto.
    destruct Hmrfe1 as [Hrf1 ?].
    generalize (rf_uni X y wy w1 Hrfwf Hrf Hrf1); intro Heq.
    rewrite Heq in Hws2; generalize (ws_trans E X x w1 w2 Hwswf Hws1 Hws2); intro Hws.
    left; right; exists w2; split; auto.

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    inversion Hmrfi1.
    destruct Hmrfe1 as [Hrf1 ?].
    generalize (rf_uni X y wy w1 Hrfwf Hrf Hrf1); intro Heq.
    rewrite Heq in Hws2; generalize (ws_trans E X x w1 w2 Hwswf Hws1 Hws2); intro Hws.
    left; right; exists w2; split; auto.

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    destruct Hmrfi1 as [Hrf1 ?].
    generalize (rf_uni X y wy w1 Hrfwf Hrf Hrf1); intro Heq.
    rewrite Heq in Hws2; generalize (ws_trans E X x w1 w2 Hwswf Hws1 Hws2); intro Hws.
    left; right; exists w2; split; auto.
    inversion Hmrfe1.

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    inversion Hmrfi1.
    inversion Hmrfe1.
Qed.

Lemma fr_mrf_fr_mrf_implies_mhb' :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (fr E X) (mrf X) x y ->
  rel_seq (fr E X) (mrf X) y z ->
  mhb' E X x z.
Proof.
case_eq inter; case_eq intra; intros Hintra Hinter; 
unfold mhb'; unfold mrf; unfold mrfi; unfold mrfe; 
rewrite Hinter; rewrite Hintra; simpl; intros E X x y z Hwf Hs Hxy Hyz;
generalize Hs; intros [Hwswf Hrfwf];
destruct Hxy as [w1 [[Hex [Hey1 [wx [Hrf1 Hws1]]]] Hmrf1]]; destruct Hyz as [w2 [[Hey2 [Hez [wy2 [Hrf2 Hws2]]]] Hmrf2]].

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    destruct Hmrfi1 as [Hrfi1 ?].
    generalize (rf_uni X y wy2 w1 Hrfwf Hrf2 Hrfi1); intro Heq.
    assert (fr E X x w2) as Hfr.
      split; auto; split; auto.
      exists wx; split; auto.
        rewrite Heq in Hws2; apply (ws_trans E X wx w1 w2); auto.
    right; exists w2; split; auto.
    destruct Hmrfe1 as [Hrfe1 ?].
    generalize (rf_uni X y wy2 w1 Hrfwf Hrf2 Hrfe1); intro Heq.
    assert (fr E X x w2) as Hfr.
      split; auto; split; auto.
      exists wx; split; auto.
        rewrite Heq in Hws2; apply (ws_trans E X wx w1 w2); auto.
    right; exists w2; split; auto.

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    inversion Hmrfi1.
    destruct Hmrfe1 as [Hrfe1 ?].
    generalize (rf_uni X y wy2 w1 Hrfwf Hrf2 Hrfe1); intro Heq.
    assert (fr E X x w2) as Hfr.
      split; auto; split; auto.
      exists wx; split; auto.
        rewrite Heq in Hws2; apply (ws_trans E X wx w1 w2); auto.
    right; exists w2; split; auto.

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    destruct Hmrfi1 as [Hrfi1 ?].
    generalize (rf_uni X y wy2 w1 Hrfwf Hrf2 Hrfi1); intro Heq.
    assert (fr E X x w2) as Hfr.
      split; auto; split; auto.
      exists wx; split; auto.
        rewrite Heq in Hws2; apply (ws_trans E X wx w1 w2); auto.
    right; exists w2; split; auto.
    inversion Hmrfe1.

  inversion Hmrf1 as [Hmrfi1 | Hmrfe1].
    inversion Hmrfi1.
    inversion Hmrfe1.
Qed.

Lemma mhb'_trans :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  mhb' E X x y ->
  mhb' E X y z ->
  mhb' E X x z.
Proof.
intros E X x y z Hwf Hs Hxy Hyz;
generalize Hs; intros [Hwswf Hrfwf].
generalize (mhb'_dec Hwf Hs Hxy); intro Horxy.
generalize (mhb'_dec Hwf Hs Hyz); intro Horyz.
  inversion Horxy as [Hmhbxy | Huxy]; inversion Horyz as [Hmhbyz | Huyz].
    eapply mhb_seq_mhb_implies_mhb'; [apply Hwf | apply Hs | apply Hmhbxy | apply Hmhbyz].
    inversion Huyz as [Hwssyz | Hfrsyz].
    eapply mhb_seq_ws_rf_implies_mhb'; [apply Hwf | apply Hs | apply Hmhbxy | apply Hwssyz].
    eapply mhb_seq_fr_mrf_implies_mhb'; [apply Hs | apply Hmhbxy | apply Hfrsyz].

    inversion Huxy as [Hwssxy | Hfrsxy].
    eapply ws_mrf_seq_mhb_implies_mhb'; [apply Hs | apply Hwssxy | apply Hmhbyz].
    eapply fr_mrf_seq_mhb_implies_mhb'; [apply Hwf | apply Hs | apply Hfrsxy | apply Hmhbyz].

    inversion Huxy as [Hwssxy | Hfrsxy]; inversion Huyz as [Hwssyz | Hfrsyz].
    destruct Hwssxy as [? [Hws_x Hrf_y]];
    destruct Hwssyz as [? [Hws_y Hrf_z]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_mrf_is_read E Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x1 Hwswf Hws_y); intros [? [? Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    eapply ws_mrf_fr_mrf_implies_mhb'; auto.
      apply Hwssxy. apply Hfrsyz.
    destruct Hrfwf as [? [Hrf_cands ?]].
    destruct Hfrsxy as [? [? Hmrf]]; destruct Hwssyz as [? [Hws ?]];
    generalize (ran_mrf_is_read E Hrf_cands Hmrf); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x1 Hwswf Hws); intros [? [? Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    eapply fr_mrf_fr_mrf_implies_mhb'; auto.
      apply Hfrsxy. apply Hfrsyz.
Qed.

Lemma mhb'_in_hb' :
  forall E X,
  rel_incl (mhb' E X) (hb' E X).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra; unfold mhb'; 
unfold mrf; unfold mhb; unfold mrfi; unfold mrfe;
rewrite Hinter; rewrite Hintra; intros E X x y Hxy.

inversion Hxy as [Hr | Hs].
  inversion Hr as [Hre | Hu].
    inversion Hre as [Hrfe | Hres].
      left; left; left; left; destruct Hrfe; auto.
      inversion Hres as [Hrfi | Hu].
        left; left; left; left; destruct Hrfi; auto.
        inversion Hu as [Hws | Hfr].
        left; left; right; auto. left; left; left; right; auto.
  simpl in Hu; destruct Hu as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  left; right; exists z; split; auto. destruct Hrfi; auto. destruct Hrfe; auto. 
  simpl in Hs; destruct Hs as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  right; exists z; split; auto. destruct Hrfi; auto. destruct Hrfe; auto. 

inversion Hxy as [Hr | Hs].
  inversion Hr as [Hre | Hu].
    inversion Hre as [Hrfe | Hres].
      left; left; left; left; destruct Hrfe; auto.
        inversion Hres as [Hws | Hfr].
        left; left; right; auto. left; left; left; right; auto.
  simpl in Hu; destruct Hu as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  left; right; exists z; split; auto. inversion Hrfi. destruct Hrfe; auto. 
  simpl in Hs; destruct Hs as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  right; exists z; split; auto. inversion Hrfi; auto. destruct Hrfe; auto. 

inversion Hxy as [Hr | Hs].
  inversion Hr as [Hre | Hu].
    inversion Hre as [Hrfe | Hres].
      left; left; left; left; destruct Hrfe; auto.
        inversion Hres as [Hws | Hfr].
        left; left; right; auto. left; left; left; right; auto.
  simpl in Hu; destruct Hu as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  left; right; exists z; split; auto. destruct Hrfi; auto. inversion Hrfe.  
  simpl in Hs; destruct Hs as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  right; exists z; split; auto. destruct Hrfi; auto. inversion Hrfe.  

inversion Hxy as [Hr | Hs].
  inversion Hr as [Hre | Hu].
        inversion Hre as [Hws | Hfr].
        left; left; right; auto. left; left; left; right; auto.
  simpl in Hu; destruct Hu as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  left; right; exists z; split; auto. inversion Hrfi. inversion Hrfe.  
  simpl in Hs; destruct Hs as [z [Hxz Hzy]]; inversion Hzy as [Hrfi | Hrfe];
  right; exists z; split; auto. inversion Hrfi. inversion Hrfe.  
Qed.

Lemma mhb'_ac :
  forall E X x,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(mhb' E X x x).
Proof.
unfold not;
intros E X x Hvalid Hx.
generalize (mhb'_in_hb' Hx); intro Hhb.
apply (hb'_ac Hvalid Hhb).
Qed.

Lemma ac_mhb'_u_ppo :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, rel_union (mhb' E X) (ppo E) x x).
unfold not;
intros E X Hwf Hs [x Hx].
inversion Hx as [Hhb | Hpo].
  generalize (mhb'_ac Hs Hhb); trivial.
  generalize (ppo_ac Hwf Hpo); trivial.
Qed.

Lemma mhb_union_ppo_cycle_implies_mhb'_seq_ppo_cycle2 : (*2*)
  forall E X x,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (tc (rel_union (mhb E X) (ppo E))) x x ->
  (exists y, (tc (rel_seq (maybe (mhb' E X)) (tc (ppo E)))) y y).
Proof.
intros E X x Hwf Hvalid Hc.
eapply union_cycle_implies_seq_cycle'. 
apply (ac_mhb_u_ppo X Hwf Hvalid).
unfold not; intros [e Hppo]. 
generalize (ppo_ac); intro thm; unfold not in thm; apply (thm E e Hwf Hppo).
unfold not; intros [e Hmhb].
generalize (mhb'_ac); intro thm; unfold not in thm; apply (thm E X e Hvalid Hmhb).
unfold trans; intros; eapply mhb'_trans; auto.
  apply H. apply H0.
left; left; auto.
apply Hc.
Qed.

Lemma mhb_union_ppo_sub_cycle_implies_mhb'_seq_ppo_sub_cycle : (*2*)
  forall E X x, forall r,
  trans r ->
  ~(exists x, rel_union (mhb E X) r x x) ->
  ~(exists x, r x x) ->
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (tc (rel_union (mhb E X) r)) x x ->
  (exists y, (tc (rel_seq (mhb' E X) r)) y y).
Proof.
intros E X x r Htr Hacu Hacr Hwf Hvalid Hc.
eapply union_cycle_implies_seq_cycle.
apply Hacu.
unfold not; intros [e Hppo]. 
apply Hacr; exists e; auto.
unfold not; intros [e Hmhb].
generalize (mhb'_ac); intro thm; unfold not in thm; apply (thm E X e Hvalid Hmhb).
unfold trans; intros; eapply mhb'_trans; auto.
  apply H. apply H0.
apply Htr; auto.
left; left; auto.
apply Hc.
Qed.*)

Definition po_tso (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 => (po_iico E) e1 e2 /\
    (reads E e1 \/ (writes E e1 /\ writes E e2)).
Definition com_tso (E:Event_struct) (X:Execution_witness) : Rln Event :=
  rel_union (rel_union (ws X) (fr E X)) (rfe X).
Definition com'_tso (E:Event_struct) (X:Execution_witness) : Rln Event :=
  rel_union (rel_union (com_tso E X) (rel_seq (ws X) (rfe X)))
  (rel_seq (fr E X) (rfe X)).

Lemma com_tso_in_com :
  forall E X x y,
  well_formed_event_structure E ->
  com_tso E X x y ->
  com E X x y.
Proof.  
intros E X x y Hwf Hxy.
inversion Hxy as [Hws_fr | Hrf].
  inversion Hws_fr as [Hws | Hfr].
    right; auto.
    left; right; auto.
    destruct Hrf; left; left; auto.
Qed.

Lemma po_com_tso_in_po_com :
  forall E X,
  well_formed_event_structure E ->
  Included _ (udr (rel_union (po_tso E) (com_tso E X))) 
    (udr (rel_union (po_iico E) (com E X))).
Proof.
intros E X Hwf x Hx.
  inversion Hx as [e Hd | e Hr].
    destruct Hd as [y Hord]; unfold udr; apply incl_union_left_in; exists y.
      inversion Hord as [Hpo | Hhb].
        left; destruct Hpo; auto.
        right; apply (com_tso_in_com Hwf Hhb).
    destruct Hr as [y Horr]; unfold udr; apply incl_union_right_in; exists y.
      inversion Horr as [Hpo | Hhb].
        left; destruct Hpo; auto.
        right; apply (com_tso_in_com Hwf Hhb).
Qed.

Lemma com'_tso_in_com' :
  forall E X x y,
  well_formed_event_structure E ->
  com'_tso E X x y ->
  com' E X x y.
Proof.  
intros E X x y Hwf Hxy.
inversion Hxy as [Hhb_wsrf | Hrf_fr].
  inversion Hhb_wsrf as [Hhb | Hws_rf].
  left; left; apply com_tso_in_com; auto.
  left; right; destruct Hws_rf as [z [Hws Hrf]]; exists z; split;
  destruct Hrf; auto.
  right; destruct Hrf_fr as [z [Hfr Hrf]]; exists z; split;
  destruct Hrf; auto.
Qed.

Lemma com_tso_in_com'_tso :
  forall E X x y,
  well_formed_event_structure E ->
  com_tso E X x y ->
  com'_tso E X x y.
Proof.  
intros E X x y Hwf Hxy.
inversion Hxy as [Hws_fr | Hrf].
  inversion Hws_fr as [Hws | Hfr].
    left; left; auto.
    left; left; auto.
    destruct Hrf; left; left; auto.
Qed.

Lemma po_tso_trans :
  forall E x y z,
  well_formed_event_structure E ->
  (po_tso E) x y ->
  (po_tso E) y z ->
  (po_tso E) x z.
Proof.
unfold po_tso;
intros E x y z Hwf [Hxy Horx] [Hyz Hory].
inversion Hxy as [Hpo_xy | Hiico_xy];
inversion Hyz as [Hpo_yz | Hiico_yz].
  split; auto. left; eapply pos_trans; eauto.
    inversion Horx; auto.
    inversion Hory; destruct H as [Hwx Hwy].
      destruct Hwy as [? [ly [vy Hwy]]];
      destruct H0 as [? [l [v Hry]]]; rewrite Hry in Hwy; inversion Hwy.
      right; destruct H0; auto. 
  split. left; eapply po_iico_trans; eauto.
    inversion Horx; auto.
    inversion Hory; destruct H as [Hwx Hwy].
      destruct Hwy as [? [ly [vy Hwy]]];
      destruct H0 as [? [l [v Hry]]]; rewrite Hry in Hwy; inversion Hwy.
      right; destruct H0; auto. 
  split. left; eapply iico_po_trans; eauto.
    inversion Horx; auto.
    inversion Hory; destruct H as [Hwx Hwy].
      destruct Hwy as [? [ly [vy Hwy]]];
      destruct H0 as [? [l [v Hry]]]; rewrite Hry in Hwy; inversion Hwy.
      right; destruct H0; auto. 
  split. right; eapply iico_trans; eauto.
    inversion Horx; auto.
    inversion Hory; destruct H as [Hwx Hwy].
      destruct Hwy as [? [ly [vy Hwy]]];
      destruct H0 as [? [l [v Hry]]]; rewrite Hry in Hwy; inversion Hwy.
      right; destruct H0; auto. 
Qed.

Lemma ac_u_tso :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, rel_union (com_tso E X) (po_tso E) x x).
unfold not;
intros E X Hwf Hvalid [x Hx].
inversion Hx as [Hhb | Hpo].
    assert (com E X x x) as Hin.
      apply com_tso_in_com; auto.
  generalize (com_ac Hvalid Hin); trivial.
    destruct Hpo as [Hpo ?].
  generalize (po_ac Hwf Hpo); trivial.
Qed.

Lemma com_tso_seq_com_tso_implies_com'_tso :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com_tso E X x y ->
  com_tso E X y z ->
  com'_tso E X x z.
Proof.
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.
inversion Hxy as [Hws_fr_xy | Hrf_xy];
inversion Hyz as [Hws_fr_yz | Hrf_yz].
  inversion Hws_fr_xy as [Hws_xy | Hfr_xy];
  inversion Hws_fr_yz as [Hws_yz | Hfr_yz].
    left; left; left; left;
    apply (ws_trans E X x y z Hwswf Hws_xy Hws_yz).

    left; right; exists y; split; auto.
    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  

    destruct Hfr_xy as [? [? [wr [Hrf Hws]]]].
    generalize (ws_trans E X wr y z Hwswf Hws Hws_yz); intro Hws_wrz.
    left; left; left; right.
    eapply fr_ax2; [apply Hwf | | exists wr; split; auto]; split; auto.

    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr_yz); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  

    inversion Hws_fr_xy as [Hws_xy | Hfr_xy].
    left; right; exists y; split; auto.

    right; exists y; auto.

    inversion Hws_fr_yz as [Hws_yz | Hfr_yz].
    destruct Hrf_xy as [Hrf_xy ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

    generalize (fr_ax1 Hfr_yz); intros [wr [Hrf Hws]].
    destruct Hrf_xy as [Hrf_xy ?].
    generalize (rf_uni X y x wr Hrfwf Hrf_xy Hrf); intro Heq.
    rewrite <- Heq in Hws; left; left; left; left; apply Hws.

    destruct Hrf_xy as [Hrf_xy ?].
    destruct Hrf_yz as [Hrf_yz ?].   
    destruct Hrfwf as [? [Hrf_cands ?]].    
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
Qed.

Lemma com_tso_seq_ws_rf_implies_com'_tso :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com_tso E X x y ->
  rel_seq (ws X) (rfe X) y z ->
  com'_tso E X x z.
Proof.
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.
inversion Hxy as [Hws_fr_xy | Hrf_xy].
  inversion Hws_fr_xy as [Hws_xy | Hfr_xy].
      destruct Hyz as [wz [Hws_ywz Hrfwz]].
      generalize (ws_trans E X x y wz Hwswf Hws_xy Hws_ywz); intro Hws_xwz.
      left; right; exists wz; split; auto.

      destruct Hyz as [wz [Hws_ywz Hrfwz]].
      destruct Hfr_xy as [? [? [wx [Hrf_wx Hws_wxy]]]].
      generalize (ws_trans E X wx y wz Hwswf Hws_wxy Hws_ywz); intro Hws_wxwz.
      right; exists wz; split; [|apply Hrfwz].
      eapply fr_ax2; 
        [apply Hwf | | exists wx; split; [apply Hrf_wx | apply Hws_wxwz]]; split; auto.
      destruct Hyz as [wz [Hws_ywz Hrfwz]].

    destruct Hrf_xy as [Hrf_xy ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x y Hrf_cands Hrf_xy); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y wz Hwswf Hws_ywz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.  
Qed.

Lemma ws_rf_seq_com_tso_implies_com'_tso :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (ws X) (rfe X) x y ->
  com_tso E X y z ->
  com'_tso E X x z.
Proof.
intros E X x y z [Hwswf Hrfwf] Hxy Hyz.
inversion Hyz as [Hws_fr_yz | Hrf_yz].
  inversion Hws_fr_yz as [Hws_yz | Hfr_yz].
    destruct Hxy as [? [Hws Hrf]].
    destruct Hrf as [Hrf ?].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.   

      destruct Hxy as [wy1 [Hws_xwy1 Hrf_wy1]].
      generalize (fr_ax1 Hfr_yz); intros [wy2 [Hrf_y2 Hws_z]].
      destruct Hrf_wy1 as [Hrf_wy1 ?].
      generalize (rf_uni X y wy1 wy2 Hrfwf Hrf_wy1 Hrf_y2); intro Heq.
        rewrite <- Heq in Hws_z.
        left; left; left; left; eapply ws_trans; [ apply Hwswf | apply Hws_xwy1 | apply Hws_z].

    destruct Hxy as [? [Hws Hrf]].
    destruct Hrf as [Hrf ?].
    destruct Hrfwf as [? [Hrf_cands ?]].    
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    destruct Hrf_yz as [Hfr_yz ?].
    generalize (dom_rf_is_write E X y z Hrf_cands Hfr_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.   
Qed.

Lemma com_tso_seq_fr_rf_implies_com'_tso :
  forall E X x y z,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com_tso E X x y ->
  rel_seq (fr E X) (rfe X) y z ->
  com'_tso E X x z.
Proof.
intros E X x y z [Hwswf Hrfwf] Hxy Hyz.
inversion Hxy as [Hws_fr_xy | Hrf_xy].
  inversion Hws_fr_xy as [Hws_xy | Hfr_xy].

    destruct Hyz as [? [Hfr Hrf]].
    generalize (ran_ws_is_write E X x y Hwswf Hws_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.

    destruct Hyz as [? [Hfr Hrf]].
    generalize (ran_fr_is_write Hwswf Hfr_xy); intros [l [v Hwy]].
    generalize (dom_fr_is_read Hrfwf Hfr); intros [ly [vy Hry]].
    rewrite Hwy in Hry; inversion Hry.  

    destruct Hyz as [wz [Hfr Hrf]].
    destruct Hfr as [? [? [wy [Hrf_y Hws_z]]]].
    destruct Hrf_xy as [Hrf_xy ?].
    generalize (rf_uni X y x wy Hrfwf Hrf_xy Hrf_y); intro Heq.
    rewrite <- Heq in Hws_z.
    left; right; exists wz; split; auto.
Qed.

Lemma fr_rf_seq_com_tso_implies_com'_tso :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_seq (fr E X) (rf X) x y ->
  com_tso E X y z ->
  com'_tso E X x z.
Proof.
intros E X x y z Hwf [Hwswf Hrfwf] Hxy Hyz.
inversion Hyz as [Hws_fr_yz | Hrf_yz].
  inversion Hws_fr_yz as [Hws_yz | Hfr_yz].

    destruct Hxy as [? [Hfr Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y z Hwswf Hws_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.

    destruct Hxy as [? [Hfr Hrf]].
    destruct Hfr as [? [? [wx [Hrf_x Hws_wx]]]].
    destruct Hfr_yz as [? [? [wy [Hrf_y Hws_wyz]]]].
    generalize (rf_uni X y x0 wy Hrfwf Hrf Hrf_y); intro Heq.
    rewrite <- Heq in Hws_wyz.
    generalize (ws_trans E X wx x0 z Hwswf Hws_wx Hws_wyz); intro Hws_wxz.
    left; left; left; right; eapply fr_ax2; [apply Hwf | | exists wx; split; [apply Hrf_x | apply Hws_wxz]]; split; auto.

    destruct Hxy as [? [Hfr Hrf]].
    destruct Hrfwf as [? [Hrf_cands ?]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf); intros [l [v Hry]].
    destruct Hrf_yz as [Hrf_yz ?].
    generalize (dom_rf_is_write E X y z Hrf_cands Hrf_yz); intros [ly [vy Hwy]].
    rewrite Hwy in Hry; inversion Hry.
Qed.

Lemma com'_tso_trans :
  forall E X x y z,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com'_tso E X x y ->
  com'_tso E X y z ->
  com'_tso E X x z.
Proof.
intros E X x y z Hwf Hvalid Hxy Hyz.
inversion Hxy as [Hpxy | Hfrrf_xy];
inversion Hyz as [Hpyz | Hfrrf_yz].
  inversion Hpxy as [Hhb_xy | Hwsfr_xy];
  inversion Hpyz as [Hhb_yz | Hwsfr_yz].
    eapply com_tso_seq_com_tso_implies_com'_tso; [apply Hwf | apply Hvalid | apply Hhb_xy | apply Hhb_yz].
    eapply com_tso_seq_ws_rf_implies_com'_tso; [apply Hwf | apply Hvalid | apply Hhb_xy | apply Hwsfr_yz ].
    eapply ws_rf_seq_com_tso_implies_com'_tso; [apply Hvalid | apply Hwsfr_xy | apply Hhb_yz].
    destruct Hwsfr_xy as [? [Hws_x Hrf_y]];
    destruct Hwsfr_yz as [? [Hws_y Hrf_z]].
      destruct Hrf_y as [Hrf_y ?].
    destruct Hvalid as [Hwswf [? [Hrf_cands ?]]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x1 Hwswf Hws_y); intros [? [? Hwy]].
    rewrite Hwy in Hry; inversion Hry.
  inversion Hpxy as [Hhb_xy | Hwsfr_xy].
    eapply com_tso_seq_fr_rf_implies_com'_tso; [apply Hvalid | apply Hhb_xy | apply Hfrrf_yz].
    destruct Hfrrf_yz as [wz [Hfr_y Hrf_z]];
    destruct Hwsfr_xy as [wy1 [Hws_x Hrf_y1]].
     destruct Hfr_y as [? [? [wy2 [Hrf_y2 Hws_wz]]]].
     destruct Hrf_y1 as [Hrf_y1 ?].
    destruct Hvalid as [Hwswf Hrfwf].
     generalize (rf_uni X y wy1 wy2 Hrfwf Hrf_y1 Hrf_y2); intro Heq.
     rewrite <-  Heq in Hws_wz.
     generalize (ws_trans E X x wy1 wz Hwswf Hws_x Hws_wz); intro Hws_xwz.
     left; right; exists wz; split; auto.
  inversion Hpyz as [Hhb_yz | Hwsfr_yz].
    eapply fr_rf_seq_com_tso_implies_com'_tso; [apply Hwf | apply Hvalid | (*apply Hfrrf_xy*) | apply Hhb_yz].
      destruct Hfrrf_xy as [e [Hfr [Hrf ?]]]; exists e; split; auto.
    destruct Hfrrf_xy as [? [Hfr_x Hrf_y]].
    destruct Hwsfr_yz as [? [Hws_y Hrf_z]].
    destruct Hrf_y as [Hrf_y ?].
    destruct Hvalid as [Hwswf [? [Hrf_cands ?]]].
    generalize (ran_rf_is_read E X x0 y Hrf_cands Hrf_y); intros [l [v Hry]].
    generalize (dom_ws_is_write E X y x1 Hwswf Hws_y); intros [? [? Hwy]].
    rewrite Hwy in Hry; inversion Hry.
    destruct Hfrrf_xy as [wy1 [Hfr_x Hrf_y]];
    destruct Hfrrf_yz as [wz [Hfr_y Hrf_z]].
     destruct Hfr_y as [? [? [wy2 [Hrf_y2 Hws_wz]]]].
     destruct Hfr_x as [? [? [wx [Hrf_x Hws_x]]]].
    destruct Hrf_y as [Hrf_y ?].
    generalize Hvalid; intros [Hwswf Hrfwf].
     generalize (rf_uni X y wy1 wy2 Hrfwf Hrf_y Hrf_y2); intro Heq.
     rewrite <- Heq in Hws_wz.
     generalize (ws_trans E X wx wy1 wz Hwswf Hws_x Hws_wz); intro Hws_wxwz.
    assert (exists wr : Event, rf X wr x /\ ws X wr wz) as Hfrax_xwz.
      exists wx; split; auto.
     generalize (fr_ax2 X x wz Hwf Hvalid Hfrax_xwz); intro Hfr_xwz.
     right; exists wz; split; auto.
Qed.

Lemma com_tso_union_po_tso_cycle_implies_com'_tso_seq_po_tso_cycle :
  forall E X x,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (tc (rel_union (com_tso E X) (po_tso E))) x x ->
  (exists y, (tc (rel_seq (com'_tso E X) (po_tso E))) y y).
Proof.
intros E X x Hwf Hvalid Hc.
eapply union_cycle_implies_seq_cycle.
apply (ac_u_tso Hwf Hvalid).
unfold not; intros [e Hpo]. 
generalize (po_ac); intro thm; unfold not in thm; apply (thm E e Hwf).
  destruct Hpo; auto.
unfold not; intros [e Hhb]. 
generalize (com'_ac); intro thm; unfold not in thm; apply (thm E X e Hvalid).
apply com'_tso_in_com'; auto.
unfold trans; intros; eapply com'_tso_trans; auto.
  apply H. apply H0. 
unfold trans; intros; eapply po_tso_trans; auto.
  apply H. apply H0.
left; left. apply H.
apply Hc.
Qed.

Lemma com'_dom_in_evts :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (com' E X) x y ->
  In _ (events E) x.
Proof.
intros E X x y Hwf Hvalid Hhb'.
inversion Hhb' as [Hhb_wsrf | Hfrrf].
  inversion Hhb_wsrf as [Hhb | Hwsrf].
  eapply com_dom_in_evts; [apply Hwf | apply Hvalid | apply Hhb].
  destruct Hwsrf as [? [Hws ?]].
  destruct Hvalid as [Hwswf Hrfwf];
  eapply dom_ws_in_events; [apply Hwf | apply Hwswf | apply Hws].
  destruct Hfrrf as [? [Hfr ?]].
  eapply dom_fr_in_events; [apply Hwf | apply Hfr].
Qed.

Lemma com'_ran_in_evts :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (com' E X) x y ->
  In _ (events E) y.
Proof.
intros E X x y Hwf Hvalid Hhb'.
inversion Hhb' as [Hhb_wsrf | Hfrrf].
  inversion Hhb_wsrf as [Hhb | Hwsrf].
  eapply com_ran_in_evts; [apply Hwf | apply Hvalid | apply Hhb].
  destruct Hwsrf as [? [Hws Hrf]].
  destruct Hvalid as [Hwswf Hrfwf];
  eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
  destruct Hfrrf as [? [Hfr Hrf]].
  destruct Hvalid as [Hwswf Hrfwf];
  eapply ran_rf_in_events; [apply Hwf | apply Hrfwf | apply Hrf].
Qed.

(*Lemma ws_u_fr_seq_ab_path_implies_ghb_path :
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  tc (rel_union (rel_seq (rel_union (ws X) (fr E X)) (abc E X)) (abc E X)) x y ->
  tc (ghb E X) x y.
Proof.
intros E X x y Hwf Hvalid Hxy.
induction Hxy.
  inversion H as [Hwsfr_ab | Hab_xy].
    destruct Hwsfr_ab as [z [Hws_u_fr_xz Hab_zy]].
    apply trc_ind with z; apply trc_step.
      apply (ws_u_fr_in_ghb Hvalid Hws_u_fr_xz).
      apply (ab_in_ghb Hab_zy).
    apply trc_step; apply (ab_in_ghb Hab_xy).
  apply trc_ind with z; auto.
Qed.*)

End Hexa.

Section Obs.
Import util.
Lemma in_rr_or :
  forall E X l x e,
  (rrestrict (ws X) (writes_to_same_loc_l (events E) l)) x e \/
  (rrestrict (ws X) (writes_to_same_loc_l (events E) l)) e x ->
  x <> e ->
  ws X x e \/ ws X e x.
Proof.
intros E X l x e Hor Hdiff.
inversion Hor as [Hxe | Hex].
left; destruct Hxe as [Hws Hrest]; apply Hws.
right; destruct Hex as [Hws Hrest]; apply Hws.
Qed.

Lemma ws_tot :
  forall E X l x e,
  linear_strict_order
            (rrestrict (ws X) (writes_to_same_loc_l (events E) l))
            (writes_to_same_loc_l (events E) l) ->
  In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) e ->
  x <> e ->
  ws X x e \/ ws X e x.
Proof.
intros E X l x e Hlin Hin Hdiff; destruct Hlin as [Hdr [Htrans [Hac Htot]]];
destruct Hin as [Hx He].
apply (in_rr_or E X (Htot x e Hdiff Hx He) Hdiff).
Qed.

End Obs.

Import util.
(*Lemma topo_ordering_correct :
  forall r S,  
  Included _ (Union Event (dom r) (ran r)) S ->
    acyclic r -> 
    (exists so,
      linear_strict_order so S /\
      rel_incl r so).
Proof.
intros r S Hincl Hac; unfold acyclic in Hac.
exists (LE (tc r)).
assert (partial_order (tc r) (Union _ (dom r) (ran r))) as Hpart.
  split.
    rewrite (dom_ran_tc r); intro x; trivial.
    split; auto.
    intros x1 x2 x3 [H12 H23]; apply trc_ind with x2; auto.
generalize (OE Hincl Hpart); intros [? ?]; split; auto.
apply (rel_incl_trans) with (tc r).
intros x y Hxy; apply trc_step; apply Hxy.
apply H.
Qed.

Lemma udr_r_in_udr_le :
  forall r x,
  rel_incl r (LE r) ->
  In _ (Union _ (dom r) (ran r)) x ->
  In _ (Union _ (dom (LE r)) (ran (LE r))) x.
Proof.
intros r x Hincl Hin; inversion Hin as [e Hd | e Hr]; [left | right].
  destruct Hd as [y Hd]; exists y; apply Hincl; auto.
  destruct Hr as [y Hr]; exists y; apply Hincl; auto.  
Qed.*)

Lemma com_implies_same_loc :
  forall E X e1 e2, 
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X e1 e2 -> loc e1 = loc e2.
Proof.
intros E X e1 e2 Hwf [Hwfws Hwfrf] Hhb;
inversion Hhb as [Hrffr | Hws].
  inversion Hrffr as [Hrf | Hfr].
    eapply rf_implies_same_loc2; [split; [apply Hwfws | apply Hwfrf] | apply Hrf].
    eapply fr_implies_same_loc; [split; [apply Hwfws | apply Hwfrf] | apply Hfr].
    eapply ws_implies_same_loc; [split; [apply Hwfws | apply Hwfrf] | apply Hws].    
Qed.

Lemma com'_implies_same_loc :
  forall E X e1 e2, 
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com' E X e1 e2 -> loc e1 = loc e2.
Proof.
intros E X e1 e2 Hwf Hs Hhb';
inversion Hhb' as [Hu | Hfrrf].
inversion Hu as [Hhb | Hwsrf].
  apply com_implies_same_loc with E X; auto.
  destruct Hwsrf as [e [Hws Hrf]].
    rewrite (ws_implies_same_loc X e1 e Hs Hws).
    apply rf_implies_same_loc2 with E X; auto.
  destruct Hfrrf as [e [Hfr Hrf]].
    rewrite (fr_implies_same_loc Hs Hfr).
    apply rf_implies_same_loc2 with E X; auto.
Qed.

Lemma com_implies_writes :
  forall E X e1 e2, 
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X e1 e2 -> writes E e1 \/ writes E e2.
Proof.
  intros E X e1 e2 Hwf [Hwswf Hrfwf] Hhb.
  inversion Hhb as [Hrffr | Hws].
    inversion Hrffr as [Hrf | Hfr].
      generalize Hrfwf; intro Hbis.
      destruct Hrfwf as [? [Hrf_cands ?]].
      left; unfold writes; split; [
        eapply dom_rf_in_events; auto; [apply Hbis| apply Hrf] |
        eapply dom_rf_is_write; [apply Hrf_cands | apply Hrf]].
      destruct Hfr as [He1 [He2 [w [Hrf Hws]]]].
      destruct Hrfwf as [? [Hrf_cands ?]].
      right; unfold writes; split; [
        eapply ran_ws_in_events; auto; [apply Hwswf | apply Hws] | ].
      generalize (ran_ws_is_write E X w e2 Hwswf Hws); intros [v [l H2]];
      exists l; exists v; apply H2.
      right; unfold writes; split; [
        eapply ran_ws_in_events; auto; [apply Hwswf | apply Hws] | ].
      generalize (ran_ws_is_write E X e1 e2 Hwswf Hws); intros [v [l H2]];
      exists l; exists v; apply H2.
Qed.

(*Lemma com_implies_compete :
  forall E X e1 e2, 
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X e1 e2 /\ proc_of e1 <> proc_of e2 -> compete E e1 e2.
Proof.
unfold compete; intros E X e1 e2 Hwf [Hws Hrf] [Hhb Hp]; split; [|split; [|split; [|split]]].
  change (events E e1) with (In _ (events E) e1); eapply com_domain_in_events; auto.
    split; [apply Hws | apply Hrf].
    apply Hhb.
  change (events E e2) with (In _ (events E) e2); eapply com_range_in_events; auto.
    split; [apply Hws | apply Hrf].
    apply Hhb.
  eapply com_implies_same_loc; auto;
    [apply Hwf | split; [apply Hws | apply Hrf] | apply Hhb].
  auto.
  eapply com_implies_writes;
    [apply Hwf | split; [apply Hws | apply Hrf] | apply Hhb].
Qed.  *)

(*Definition bot_ghb (E:Event_struct) (X:Execution_witness) := 
  rel_union (abc E X)
        (rel_union (rel_union (ws X) (fr E X)) (ppo E)).*)

(*Lemma bot_ghb_in_ghb :
  forall E X, 
  rel_incl (bot_ghb E X) (ghb E X).
Proof.
case_eq inter; case_eq intra; 
intros Hintra Hinter E X; unfold ghb;
rewrite Hintra; rewrite Hinter; simpl.
right; right; trivial.
right; trivial.
right; trivial.
unfold bot_ghb; intros x y Hxy; trivial.
Qed.*)

Lemma not_diff_proc_class :
  forall e z, ~ proc_of e <> proc_of z -> proc_of e = proc_of z.
Proof.
intros e z Hn.
apply NNPP; auto.
Qed.

(*Lemma ghb_in_union :
  forall E X,
  rel_incl (AWmm.ghb E X)
    (rel_union (rel_union (hb E X) (po_iico E)) 
              (A.abc E X)).
Proof.
intros E X e e0 Hghb; unfold ghb in Hghb.
case_eq inter; case_eq intra; intros Hintra Hinter; 
  rewrite Hinter in Hghb; rewrite Hintra in Hghb.
  (*true true*)
  inversion Hghb as [Hrf_inter | Hrest].
    destruct Hrf_inter as [Hrf ?].
    left; left; left; left; auto.
    inversion Hrest as [Hrf_intra | Hres].
      destruct Hrf_intra as [Hrf ?].
      left; left; left; left; auto.
      inversion Hres as [Hin_ab | Hre].
        right; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
            left; left; right; auto.
            (*left; left; left; right; auto.*)
            left; right; apply ppo_valid; apply Hppo.
  (*true false*)
  inversion Hghb as [Hrf_inter | Hrest].
    destruct Hrf_inter as [Hrf ?].
    left; left; left; left; auto.
      inversion Hrest as [Hin_ab | Hre].
        right; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
            left; left; right; auto.
            (*left; left; left; right; auto.*)
          left; right; apply ppo_valid; apply Hppo.
  (*false true*)
  inversion Hghb as [Hrf_intra | Hres].
      destruct Hrf_intra as [Hrf ?].
      left; left; left; left; auto.
      inversion Hres as [Hin_ab | Hre].
        right; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
            left; left; right; auto.
            (*left; left; left; right; auto.*)
          left; right; apply ppo_valid; apply Hppo.
  (*false false*)
  inversion Hghb as [Hin_ab | Hre].
        right; auto.
        inversion Hre as [Hws_fr | Hppo].
          (*inversion Hws_fr as [Hws | Hfr].*)
            left; left; right; auto.
            (*left; left; left; right; auto.*)
          left; right; apply ppo_valid; apply Hppo.
Qed.

Lemma tc_ghb_in_union :
  forall E X,
  rel_incl (tc (AWmm.ghb E X))
    (tc (rel_union (rel_union (hb E X) (po_iico E)) 
              (A.abc E X))).
Proof.
intros E X x y; apply tc_incl.
apply ghb_in_union.
Qed.

Lemma fr_in_mhb :
  forall E X,
  rel_incl (fr E X) (mhb E X).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra; unfold mhb'; 
unfold mrf; unfold mhb; unfold mrfi; unfold mrfe;
rewrite Hinter; rewrite Hintra; intros E X x y Hxy.
  right; right; right; auto.
  right; right; auto.
  right; right; auto.
  right; auto.
Qed.

Lemma ws_in_mhb :
  forall E X,
  rel_incl (ws X) (mhb E X).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra; unfold mhb'; 
unfold mrf; unfold mhb; unfold mrfi; unfold mrfe;
rewrite Hinter; rewrite Hintra; intros E X x y Hxy.
  right; right; left; auto.
  right; left; auto.
  right; left; auto.
  left; auto.
Qed.*)

Lemma po_tc_po :
  forall E x y, 
  well_formed_event_structure E ->
  tc (po_iico E) x y ->
  po_iico E x y.
Proof.
intros E x y Hwf Hxy.
induction Hxy; auto.
apply po_trans with z; auto.
Qed.

(*Rrestrict*)

(*Lemma wfes_rrestrict_is_wfes :
  forall E r, well_formed_event_structure E ->
  well_formed_event_structure 
  (mkes (Intersection _ E.(events) r) (rrestrict (iico E) r)).
Proof.
intros E r Hwf; generalize Hwf; intro Hwfb; destruct_wfs Hwfb;
destruct Hstrans as [Hiicodom [Hac [Hpio [Hiiid Htrans]]]];
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].

  intros x y Hxy; apply (Hsws x y); inversion Hxy as [Hpoxy | Hiicoxy].
  destruct Hpoxy as [? [? [Hex Hey]]]; simpl in Hex; simpl in Hey; left; 
  split; [|split; [|split]]; auto. 
  destruct Hex; auto. destruct Hey; auto.
  simpl in Hiicoxy; destruct Hiicoxy; auto.
  right; auto.

  intros e1 e2 H1 H2; apply (Hsfr e1 e2).
  destruct H1; auto. destruct H2; auto.
  
  intros x [y Hxy]; destruct Hxy as [? [? ?]]; simpl; split; auto.
  apply po_iico_domain_in_events with y; auto.
  right; auto.

  intros x [y Hxy]; destruct Hxy as [? [? ?]]; simpl; split; auto.
  apply po_iico_range_in_events with y; auto.
  right; auto.

  simpl; apply incl_ac with (po_iico E); auto.
    intros x y [Hxy ?]; right; auto.
    intros x Hx; assert (po_iico E x x) as Hpo.
      apply po_tc_po; auto.
    apply (po_ac Hwf Hpo).

  simpl; intros x y [Hex [Hey Heq]]. 
  assert (events E x /\ events E y /\ poi (iiid x) = poi (iiid y) /\ proc_of x = proc_of y) as Hand.
    destruct Hex; destruct Hey; split; [|split]; auto.
  generalize (Hpio x y Hand); intro Hiico; simpl.
  split; [ | ]; auto. 
  destruct Hex; destruct Hey; split; auto. 

  intros e1 e2 [? ?]; apply (Hiiid e1 e2); auto.

  simpl; intros x1 x2 x3 [H12 [? ?]] [H23 [? ?]]; split; [|split]; auto.
  apply Htrans with x2; auto.
Qed.*)


Lemma po_rr :
  forall E s x y,
  well_formed_event_structure E ->
  po_iico E x y ->
  In _ s x -> In _ s y ->
  po_iico (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Proof.
intros E s x y Hwf Hxy Hx Hy.
inversion Hxy as [Hpo | Hiico]; [left | right].
  destruct Hpo as [? [? ?]]; split; [|split; [|split]]; auto.
  split; auto.
    apply po_iico_domain_in_events with y; auto.
  split; auto.
    apply po_iico_range_in_events with x; auto.

  split; auto.
Qed.

Lemma po_rr_bak :
  forall E s x y,
  well_formed_event_structure E ->
  po_iico (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y ->
  po_iico E x y.
Proof.
intros E s x y Hwf Hxy.
inversion Hxy as [Hpo | Hiico]; [left | right].
  destruct Hpo as [? [? ?]]; destruct H1 as [Hx Hy];
    destruct Hx; destruct Hy; split; [|split; [|split]]; auto.

  destruct Hiico; auto.
Qed.

(*Lemma po_rr_bak_s :
  forall E s x y,
  well_formed_event_structure E ->
  po_iico (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y ->
  s x /\ s y.
Proof.
intros E s x y Hwf Hxy.
generalize (wfes_rrestrict_is_wfes s Hwf); intro Hwfrr.
generalize (po_iico_domain_in_events Hwfrr Hxy); intro Hex.
generalize (po_iico_range_in_events Hwfrr Hxy); intro Hey.
destruct Hex; destruct Hey; split; auto.
Qed.*)

End Basic.