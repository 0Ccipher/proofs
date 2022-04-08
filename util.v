(* 

  Modified from Algalav et. TOPLAS 2014

*)

Require Import Ensembles.
Require List.

Set Implicit Arguments.

Section Class.

Lemma contraposee : forall (A B:Prop),
  (A -> B) -> (~B -> ~A).
Proof.
intros A B Himpl Hnot_b.
unfold not; unfold not in Hnot_b; intro HA; apply Hnot_b.
apply (Himpl HA).
Qed.

End Class.

Hint Resolve contraposee : util.

Section EmptySet.
Definition set := Ensemble.
Lemma empty_set_is_empty : forall (A:Set) (s:set A),
  ~(exists e, In _ s e) <-> Same_set _ (Empty_set _) s.
Proof.
intros A s.
split.
(*->*)
intros Hnon; unfold Same_set.
unfold not in Hnon; unfold In in Hnon;
unfold Included.
split; intros x Hin_empty.
elim Hnon; exists x; inversion Hin_empty.
destruct Hnon; exists x; apply Hin_empty.
(*<-*)
intros Hsame; unfold not; unfold In.
intros Hexists.
unfold Same_set in Hsame.
unfold Included in Hsame.
destruct Hsame as [Hemp_s Hs_emp].
destruct Hexists as [e Hse].
assert (In _ (Empty_set _) e).
apply (Hs_emp e Hse).
inversion H.
Qed.

Lemma empty_set_is_empty_dir : forall (A:Set) (s:set A),
  ~(exists e, In _ s e) -> Same_set _ s (Empty_set _).
Proof.
intros A s Hnot.
unfold not in Hnot.
unfold Same_set; unfold Included; split.
(*->*)
intros x Hsx.
assert (exists x, In A s x) as Hx.
exists x; exact Hsx.
assert (False) as Habs. 
apply (Hnot Hx).
contradiction.
(*<-*)
intros x.
intros Hempx.
inversion Hempx.
Qed.

Lemma empty_set_is_empty_back : forall (A:Set) (s:set A),
  Same_set _ s (Empty_set _) ->  ~(exists e, In _ s e).
Proof.
unfold not; unfold Same_set; unfold Included.
intros A s Hemp He.
destruct Hemp as [Hsemp Hemps].
destruct He as [e Hse].
assert (In A (Empty_set A) e) as Hemp.
apply (Hsemp e Hse).
inversion Hemp.
Qed.

Lemma non_empty_set_is_non_empty_dir : forall (A:Set) (s:set A),
  (exists e, In _ s e) -> ~(Same_set _ s (Empty_set _)).
Proof.
unfold not; unfold Same_set; unfold Included.
intros A s Hexists Hsame.
destruct Hsame as [Hemps Hsemp].
destruct Hexists as [e Hse].
assert (In A (Empty_set A) e) as Habs.
apply (Hemps e Hse).
inversion Habs.
Qed.

Lemma incl_is_enough_for_empty : forall (A:Set) (s:set A),
  Included _ s (Empty_set _) -> Same_set _ s (Empty_set _).
Proof.
unfold Same_set; unfold Included; unfold In.
intros A s Hemp.
split; [exact Hemp|].
intros x Habs.
inversion Habs.
Qed.

Lemma incl_is_enough_for_empty_back : forall (A:Set) (s:set A),
  Same_set _ s (Empty_set _) -> Included _ s (Empty_set _).
Proof.
unfold Same_set; unfold Included; unfold In.
intros A s Hemp.
destruct Hemp as [Hemp].
exact Hemp.
Qed.

End EmptySet.

Section Inclusion.

Lemma incl_union : forall (A:Set) (s1 s2 s:set A),
  Included _ s1 s -> Included _ s2 s -> Included _ (Union _ s1 s2) s.
Proof.
intros A s1 s2 s H1 H2.
intros x Hu.
  inversion Hu as [? Hi1 | ? Hi2].
    apply H1; auto.
    apply H2; auto.
Qed.

Lemma incl_union_in : forall (A:Set) (s1 s2 s:set A),
  Included _ s1 s -> Included _ s2 s -> 
  (forall x, In _ (Union _ s1 s2) x -> In _ s x).
Proof.
apply incl_union.
Qed.

Lemma incl_union_left_in : forall (A:Set) (s1 s2 : set A),
  forall x, In _ s1 x -> In _ (Union _ s1 s2) x.
Proof.
unfold In; intros.
apply Union_introl.
exact H.
Qed.

Lemma incl_union_right_in : forall (A:Set) (s1 s2 : set A),
  forall x, In _ s2 x -> In _ (Union _ s1 s2) x.
Proof.
unfold In; intros.
apply Union_intror.
exact H.
Qed.

Lemma incl_union_back : forall (A:Set) (s1 s2 s: set A),
  Included _ (Union _ s1 s2) s -> Included _ s1 s /\ Included _ s2 s.
Proof.
unfold Included; intros.
split.
intros.
apply (H x).
apply incl_union_left_in; exact H0.
intros.
apply (H x).
apply incl_union_right_in; exact H0.
Qed.

Lemma incl_union_back_in : forall (A:Set) (s1 s2 s: set A),
  Included _ (Union _ s1 s2) s -> 
  (forall x, In _ (Union _ s1 s2) x -> In _ s x).
Proof.
unfold Included; intros.
apply H.
exact H0.
Qed.

Lemma incl_trans : forall (A:Set) (s1 s2 s3:set A),
  Included _ s1 s2 -> Included _ s2 s3 -> Included _ s1 s3.
Proof.
unfold Included; unfold In; intros.
apply (H0 x (H x H1)).
Qed.

End Inclusion.

Section SameSet.

Lemma same_trans : forall (A:Set) (s1 s2 s3:set A),
  Same_set _ s1 s2 -> Same_set _ s2 s3 -> Same_set _ s1 s3.
Proof.
unfold Same_set; unfold Included; unfold In.
intros A s1 s2 s3 H12 H23.
destruct H12 as [H12 H21];
destruct H23 as [H23 H32].
split; intros x; [intro H1 | intro H3].
apply H23; apply H12; exact H1.
apply H21; apply H32; exact H3.
Qed.

Lemma same_refl : forall (A:Set) (s1 s2:set A),
  Same_set _ s1 s2 -> Same_set _ s2 s1.
Proof.
unfold Same_set; unfold Included; unfold In.
intros A s1 s2 H12.
destruct H12 as [H12 H21].
split; [exact H21 | exact H12].
Qed.

Lemma not_same_refl : forall (A:Set) (s1 s2:set A),
  ~(Same_set _ s1 s2) -> ~(Same_set _ s2 s1).
Proof.
unfold not; intros A s1 s2 H12 H21.
apply H12.
apply same_refl; exact H21.
Qed.

Lemma not_same_trans : forall (A:Set) (s1 s2 s3:set A),
  Same_set _ s1 s2 -> ~(Same_set _ s1 s3) -> ~(Same_set _ s2 s3).
Proof.
unfold not; intros A s1 s2 s3 H12 Hnot13 H23.
assert (Same_set A s1 s3) as H13.
eapply same_trans; [apply H12 | apply H23].
apply (Hnot13 H13).
Qed.

Lemma same_impl_incl : forall (A:Set) (s1 s2:set A),
  Same_set _ s1 s2 -> Included _ s1 s2.
Proof.
unfold Same_set; unfold Included; unfold In.
intros A s1 s2 Hsame.
destruct Hsame as [H12 H21].
exact H12.
Qed.

End SameSet.

Section LinOrder. (*w. set*)

Definition domain (A B:Set) (e:set (A*B)) : set B :=
  fun y => exists x, In _ e (x,y).

Definition range (A B:Set) (e:set (A*B)) : set A :=
  fun x => exists y, In _ e (x,y).

Lemma range_is_range : forall (A B:Set) (e:set (A*B)) (x:A),
  (exists y, In _ e (x,y)) -> In _ (range e) x.
Proof.
unfold range; unfold In; trivial.
Qed.

Lemma domain_is_domain : forall (A B:Set) (e:set (A*B)) (y:B),
  (exists x, In _ e (x,y)) -> In _ (domain e) y.
Proof.
unfold domain; unfold In; trivial.
Qed.

Definition linear_order (A:Set) (r:set (A*A)) (xs:set A) : Prop :=
  Included _ (Union _ (domain r) (range r)) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (In _ r (x1,x2)) /\ (In _ r (x2,x3)) -> (In _ r (x1,x3))) /\
  (*antisymetry*)
  (forall x1 x2, (In _ r (x1,x2)) /\ (In _ r (x2,x1)) -> x1=x2) /\
  (*linear on xs*)
  (forall x1 x2, (In _ xs x1) -> (In _ xs x2) -> ((In _ r (x1,x2)) \/ (In _ r (x2,x1)))).

Lemma linear_prop_cart : forall (A:Set) (so:set (A*A)) (s:set A) (x:A),
  (linear_order so s) -> In _ s x -> In _ s x -> In _ so (x,x).
Proof.
unfold linear_order; unfold In; intros. 
destruct H as [Hincl H].
destruct H as [Htrans H].
destruct H as [Hrefl Hlin].
assert (so (x,x) \/ so (x,x)).
apply (Hlin x x H0 H1).
inversion H.
exact H2.
exact H2.
Qed.

Lemma linear_order_trans : forall (A:Set) (so:set (A*A)) (x1 x2 x3:A),
  (exists s, (linear_order so s)) ->
  In _ so (x1,x2) -> In _ so (x2,x3) -> In _ so (x1,x3).
Proof.
intros A so x1 x2 x3 Hexists H12 H23.
unfold linear_order in Hexists.
destruct Hexists as [s He].
destruct He as [Hincl He].
destruct He as [Htrans He].
eapply Htrans.
split; [apply H12 | apply H23].
Qed.

Lemma incl_lin_order_range : forall (A:Set) (so: set (A*A)) (s:set A) (x1 x2:A),
  linear_order so s -> In _ so (x1,x2) -> In _ s x1.
Proof.
unfold linear_order; unfold In; intros.
assert (In _ (range so) x1).
apply range_is_range.
exists x2; apply H0.
assert (In _ (Union A (domain so) (range so)) x1).
apply incl_union_right_in; exact H1.
repeat (destruct H).
unfold Included in H; apply H; exact H2.
Qed.

Lemma incl_lin_order_domain : forall (A:Set) (so: set (A*A)) (s:set A) (x1 x2:A),
  linear_order so s -> In _ so (x1,x2) -> In _ s x2.
Proof.
unfold linear_order; unfold In; intros.
assert (In _ (domain so) x2).
apply domain_is_domain.
exists x1; apply H0.
assert (In _ (Union A (domain so) (range so)) x2).
apply incl_union_left_in; exact H1.
repeat (destruct H).
unfold Included in H; apply H; exact H2.
Qed.

Lemma incl_dom_ran : forall (A:Set) (so sor:set (A*A)),
  Included (A * A) sor so ->
  Included A (Union A (domain sor) (range sor))
  (Union A (domain so) (range so)).
Proof.
unfold Included;
intros A so sor Hincl x Hsor.
inversion Hsor as [y Hdom | y Hran].
(*dom*)
unfold In in Hdom; unfold domain in Hdom.
apply incl_union_left_in; unfold In; unfold domain.
destruct Hdom as [x0 Hin]; exists x0; apply (Hincl (x0,x) Hin).
(*ran*)
unfold In in Hran; unfold range in Hran.
apply incl_union_right_in; unfold In; unfold range.
destruct Hran as [x0 Hin]; exists x0; apply (Hincl (x,x0) Hin).
Qed.

End LinOrder.

(*Section LinStrictOrder.*)

Definition Rln (A:Type) := A -> A -> Prop.

Definition dom (A:Type) (r:Rln A) : set A :=
  fun x => exists y, r x y.
Definition ran (A:Type) (r:Rln A) : set A :=
  fun y => exists x, r x y.

Definition udr (A:Type) (so: Rln A) : set A :=
  Union _ (dom so) (ran so).

Definition rel_incl (A:Type) (r1 r2 : Rln A) : Prop :=
  forall x y, r1 x y -> r2 x y.

(** Linear and linear strict orders *)
Definition partial_order (A:Type) (r:Rln A) (xs:set A) : Prop :=
  Included _(Union _ (dom r) (ran r)) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\
  (*irreflexivity*)
  (forall x, ~(r x x)).

Definition linear_strict_order (A:Type) (r:Rln A) (xs:set A) : Prop :=
  Included _(Union _ (dom r) (ran r)) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\
  (*irreflexivity*)
  (forall x, ~(r x x)) /\
  (*linear on xs*)
  (forall x1 x2, (x1 <> x2) -> (In _ xs x1) -> (In _ xs x2) -> 
    (r x1 x2) \/ (r x2 x1)).
Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

Module Type OrdExt.
Parameter Elt : Type.
Parameter LE : Rln Elt -> Rln Elt.
Hypothesis OE : forall (s S:set Elt) (r:Rln Elt),
  Included _ s S ->
  partial_order r s -> 
  rel_incl r (LE r) /\
  linear_strict_order (LE r) S.
Hypothesis le_lso : forall (s:set Elt) (r:Rln Elt),
  linear_strict_order r s -> LE r = r.
End OrdExt.

Lemma linear_strict_order_trans : forall (A:Set) (so:Rln A) (x1 x2 x3:A),
  (exists s, (linear_strict_order so s)) ->
  so x1 x2 -> so x2 x3 -> so x1 x3.
Proof.
unfold linear_strict_order; unfold In; intros. 
destruct H as [s [Hdr [Htrans [Hac Htot]]]].
apply (Htrans x1 x2 x3).
split. 
exact H0.
exact H1.
Qed.

Lemma linear_strict_order_lin : forall (A:Set) (s:set A) (so:Rln A) (x1 x2:A),
  (linear_strict_order so s) ->
  (x1 <> x2) -> (In _ s x1) -> (In _ s x2) ->
  so x1 x2 \/ so x2 x1.
Proof.
intros A s so x1 x2 Hlin Hdiff H1 H2.
destruct Hlin as [Hdom [Htrans [Hacycl Hlin]]].
apply (Hlin x1 x2 Hdiff H1 H2).
Qed.

Lemma incl_lin_strict_order_dom : forall (A:Set) (so: Rln A) (s:set A) (x1 x2:A),
  linear_strict_order so s -> so x1 x2 -> In _ s x1.
Proof.
unfold linear_strict_order; unfold In; intros.
assert (In _ (dom so) x1).
exists x2; apply H0.
assert (In _ (Union A (dom so) (ran so)) x1).
apply incl_union_left_in; exact H1.
destruct H as [Hdr [Htrans [Hac Htot]]].
 unfold Included in Hdr; apply Hdr. 
exact H2.
Qed.

Lemma incl_lin_strict_order_ran : forall (A:Set) (so: Rln A) (s:set A) (x1 x2:A),
  linear_strict_order so s -> so x1 x2 -> In _ s x2.
Proof.
unfold linear_strict_order; unfold In; intros.
assert (In _ (ran so) x2).
exists x1; apply H0.
assert (In _ (Union A (dom so) (ran so)) x2).
apply incl_union_right_in; exact H1.
destruct H as [Hdr [Htrans [Hac Htot]]].
unfold Included in Hdr; apply Hdr; exact H2.
Qed.

(*End LinStrictOrder.*)

Section RRestrict.

Definition rrestrict (A:Set) (r:Rln A) (s:set A) : Rln A := 
    fun x => fun y =>
    r x y /\ In _ s x /\ In _ s y.

End RRestrict.

Section TransClos.

(** Transitive closure *)
Inductive transitive_closure (A:Type) (e:set (A*A)) : set (A*A) :=
    | t_step : forall x y, In _ e (x,y) -> In _ (transitive_closure e) (x,y)
    | t_trans : forall x y z, In _ (transitive_closure e) (x,y) -> 
                     In _ (transitive_closure e) (y,z) -> 
                     In _ (transitive_closure e) (x,z).

Inductive tc (A : Type)(r : A -> A -> Prop) : A -> A -> Prop :=
   |trc_step : forall x, forall y : A, r x y -> (tc r) x y
   |trc_ind : forall x y z : A,
      (tc r) x z ->
      (tc  r) z y -> (tc r) x y.

Inductive rc (A : Type)(r : A -> A -> Prop) : A -> A -> Prop :=
   |rc_step : forall x, forall y : A, tc r x y -> (rc r) x y
   |rc_eq : forall x y : A, x = y -> (rc r) x y.

(** Strict transitive closure *)

Definition strict (A:Set) (r:Rln A) : Rln A := 
  fun e1 => fun e2 =>
    r e1 e2 /\ e1 <> e2.

Definition stc (A:Set) (r: Rln A) : Rln A := strict (tc r).

End TransClos.

Section Acyclicity.

(** Acyclicity *)
Definition acyclic (A:Type) (r: Rln A) : Prop :=
  forall x, ~((tc r) x x).
Definition irrefl (A:Type) (r: Rln A) : Prop :=
  forall x, ~(r x x).
End Acyclicity.

Section BasicSet.

(** Union *)

Lemma union_refl : forall (A:Set) (r1 r2: set (A*A)),
  (Union _ r1 r2) = (Union _ r2 r1).
Proof.
intros A r1 r2.
apply (Extensionality_Ensembles _ (Union _ r1 r2) (Union _ r2 r1)).
unfold Same_set; unfold Included; split; intros c Hin.
inversion Hin as [c' H1 | c' H2].
  apply incl_union_right_in; exact H1.
  apply incl_union_left_in; exact H2.
inversion Hin as [c' H2 | c' H1].
  apply incl_union_right_in; exact H2.
  apply incl_union_left_in; exact H1.
Qed.

(** Cartesian product of two sets *)
Definition cartesian (A B:Set) (sa:set A) (sb:set B) : set (A*B) :=
  fun c => match c with (a,b) =>
  In _ sa a /\ In _ sb b end.

(** Topo *)

Lemma dom_tc_in_dom :
  forall (A:Set) (r: Rln A) (x:A),
  In _ (dom (tc r)) x ->
  In _ (dom r) x.
Proof.
intros A r x Hd.
destruct Hd as [y Hd].
induction Hd as [ x y Hs |x y Hi].
  exists y; apply Hs.
  exact IHHd1.
Qed.

Lemma ran_tc_in_ran :
  forall (A:Set) (r: Rln A) (x:A),
  In _ (ran (tc r)) x ->
  In _ (ran r) x.
Proof.
intros A r x Hr.
destruct Hr as [y Hr].
induction Hr as [ x y Hs |x y Hi].
  exists x; apply Hs.
  exact IHHr2.
Qed.

Lemma dom_ran_tc : 
  forall (A:Set) (r:Rln A),
  Union _ (dom r) (ran r) = Union _ (dom (tc r)) (ran (tc r)).
Proof.
intros A r.
apply (Extensionality_Ensembles _ 
  (Union _ (dom r) (ran r)) (Union _ (dom (tc r)) (ran (tc r))));
split; unfold Included; intros x Hx.
(*r -> stc r*)
inversion Hx as [e Hd | e Hr].
  apply incl_union_left_in; unfold In; unfold domain; 
    unfold In in Hd; unfold domain in Hd; destruct Hd as [y Hd].
   exists y; apply trc_step; apply Hd.
    apply incl_union_right_in; unfold In; unfold range; 
    unfold In in Hr; unfold range in Hr; destruct Hr as [y Hr].
 exists y; apply trc_step; apply Hr.
(*stc r -> r*)
induction Hx as [e Hd | e Hr].
  apply incl_union_left_in; apply dom_tc_in_dom; apply Hd.
  apply incl_union_right_in; apply ran_tc_in_ran; apply Hr.
Qed.

Definition rel_union (A:Type) (r1 r2 : Rln A) : Rln A :=
  fun x => fun y => r1 x y \/ r2 x y.

(** Maximal elements *)
Definition maximal_elements (A:Set) (xs:set A) (r:set (A*A)) : set A :=
  fun x => In _ xs x /\ forall x', In _ xs x'/\ In _ r (x, x') -> (x = x').

Lemma maximal_preserves_incl : forall (A:Set) (xs:set A) (r:set (A*A)) (e:A),
  In _ (maximal_elements xs r) e ->
  In _ xs e.
Proof.
unfold maximal_elements; unfold In.
intros A xs r e Hmax.
destruct Hmax as [Hxs].
exact Hxs.
Qed.

(** Mirror *)
Definition inv (A:Set) (r:set (A*A)) :=
  fun c => match c with (y,x) =>
  In _ r (x,y) end.

(** Singleton *)

Definition is_singleton (A:Set) (s:set A) :=
  exists e, In _ s e /\
  ~(exists e', e <> e' /\ In _ s e').

Definition is_empty (A:Set) (s:set A) := 
  Same_set _ s (Empty_set _).

End BasicSet.

Section BasicRel.

Definition emp_rel (A:Set) : Rln A :=
  fun x => fun y => False. 

Definition same_rel (A:Set) (r1 r2 : Rln A) : Prop :=
  rel_incl r1 r2 /\ rel_incl r2 r1.
Axiom ext_rel : forall (A:Type) (r1 r2 : Rln A),  
  (forall x y, r1 x y <-> r2 x y) -> r1 = r2.

Lemma incl_path :
  forall (A:Set) (r1 r2 : Rln A) (x y : A),
  rel_incl r1 r2 ->
  tc r1 x y ->
  tc r2 x y.
Proof.
intros A r1 r2 x y H12 H1.
induction H1.
  apply trc_step; apply H12; apply H.
  apply trc_ind with z; auto.
Qed.

Lemma incl_ac : 
  forall (A:Set) (r1 r2 : Rln A),
  rel_incl r1 r2 ->
  acyclic r2 ->
  acyclic r1.
Proof.
unfold acyclic; unfold not;
intros A r1 r2 H12 H2 x H1; apply (H2 x).
eapply incl_path; [apply H12 | apply H1].
Qed.

Lemma lso_is_tc :
  forall A (so:Rln A) (s: set A), 
  linear_strict_order so s -> tc so = so.
Proof.
intros A so s Hlin.
destruct Hlin as [Hdr [Htrans [Hac Htot]]].
assert (forall x y, (tc so) x y <-> so x y) as Hext.
  intros x y; split; intro Hxy.
    induction Hxy.
      apply H.
      apply (Htrans x z y); split; [apply IHHxy1 | apply IHHxy2].
    apply trc_step; apply Hxy.
apply (ext_rel (tc so) (so) Hext).
Qed.

Lemma po_is_tc :
  forall A (so:Rln A) (s: set A), 
  partial_order so s -> tc so = so.
Proof.
intros A so s Hp.
destruct Hp as [Hdr [Htrans Hac]].
assert (forall x y, (tc so) x y <-> so x y) as Hext.
  intros x y; split; intro Hxy.
    induction Hxy.
      apply H.
      apply (Htrans x z y); split; [apply IHHxy1 | apply IHHxy2].
    apply trc_step; apply Hxy.
apply (ext_rel (tc so) (so) Hext).
Qed.

Lemma lin_strict_ac :
  forall (A:Set) (s:set A) (r : Rln A),
  linear_strict_order r s -> 
  acyclic r.
Proof.
intros A s r Hlin.
generalize (lso_is_tc Hlin); intro Heq.
unfold acyclic; rewrite Heq.
destruct Hlin as [Hdr [Htrans [Hac Htot]]];
  apply Hac.
Qed.

Lemma union_triv : (*util*)
  forall (A:Type) (r1 r2 : Rln A),
  rel_union r1 r2 = rel_union r2 r1.
Proof.
intros A r1 r2.
apply ext_rel;
unfold rel_union; split; intro Hx; 
inversion Hx as [H1 | H2].
  right; apply H1.
  left; apply H2.
  right; apply H1.
  left; apply H2.
Qed.

Lemma tc_incl : forall  (E : Type)  (r1 r2 : Rln E),
  rel_incl r1 r2 -> rel_incl (tc r1) (tc r2).
Proof.
unfold rel_incl.
intros E r1 r2 ir12 x y tcr1xy.
induction tcr1xy.
  apply trc_step.
  apply ir12; trivial.
apply trc_ind with z; trivial.
Qed.

Lemma ac_incl : forall (E : Set)  (r1 r2 : Rln E),
  acyclic r2 ->  rel_incl r1 r2 -> acyclic r1.
Proof.
intros E r1 r2; unfold acyclic. intros ar2 ; unfold Included. 
intros ir12 x ixx.
assert (nar2 : tc r2 x x).
  apply (tc_incl ir12); trivial.
assert (h := ar2 x).
contradiction.
Qed.

Lemma incl_implies_union_eq :
  forall A (r1 r2: Rln A),
  rel_incl r1 r2 -> 
  rel_union r1 r2 = r2.
Proof.
unfold rel_incl; 
intros A r1 r2 Hincl.
apply ext_rel; intros x y; split; intro Hxy.
  inversion Hxy as [H1 | H2].
    apply Hincl; apply H1.
    apply H2.
  unfold rel_union; right; apply Hxy.
Qed.

Lemma incl_implies_ac_union :
  forall A (r1 r2: Rln A),
  rel_incl r1 r2 -> 
  acyclic r2 ->
  acyclic (rel_union r1 r2).
Proof.
intros A r1 r2 Hincl Hac;
generalize (incl_implies_union_eq Hincl);
intro Heq; rewrite Heq; apply Hac.
Qed.

Lemma rel_union_refl :
  forall A (r1 r2: Rln A),
  rel_union r1 r2 = rel_union r2 r1.
Proof.
intros A r1 r2.
apply ext_rel; intros x y; split; intro Hxy;
inversion Hxy as [H1 | H2].
  right; apply H1.
  left; apply H2.
  right; apply H1.
  left; apply H2.
Qed.

Lemma rel_incl_right :
  forall A (r1 r2 r3: Rln A),
  rel_incl r1 r2 ->
  rel_incl (rel_union r1 r3) (rel_union r2 r3).
Proof.
unfold rel_incl;
intros A r1 r2 r3 H12 x y H13.
inversion H13 as [H1 | H3].
  left; apply H12; apply H1.
  right; apply H3.
Qed.

Lemma rel_incl_left :
  forall A (r1 r2 r3: Rln A),
  rel_incl r1 r2 ->
  rel_incl (rel_union r3 r1) (rel_union r3 r2).
Proof.
unfold rel_incl;
intros A r1 r2 r3 H12 x y H31.
inversion H31 as [H3 | H1].
  left; apply H3.
  right; apply H12; apply H1.
Qed. 

Lemma rel_incl_trans : forall (A:Set) (r1 r2 r3 : Rln A),
  rel_incl r1 r2 -> rel_incl r2 r3 -> rel_incl r1 r3.
Proof.
unfold rel_incl;
intros A r1 r2 r3 H12 H23 x y H1.
apply H23; apply H12; apply H1.
Qed.

Definition rel_seq (A:Type) (r1 r2 : Rln A) : Rln A :=
  fun x => fun y => exists z, r1 x z /\ r2 z y.

Definition maybe (A:Type) (r:Rln A) : Rln A :=
  fun e1 => fun e2 => r e1 e2 \/ e1 = e2.

Definition phx (A:Type) (r1 r2 :Rln A) : Rln A :=
  fun e1 => fun e2 => (tc (rel_seq r1 r2)) e1 e2 \/ e1 = e2.

Definition hx (A:Type) (r1 r2:Rln A) : Rln A :=
  fun e1 => fun e2 => 
    rel_seq (maybe r2) (rel_seq (phx r1 r2) (maybe r1)) e1 e2. 

Definition phx' (A:Type) (r1 r2 :Rln A) : Rln A :=
  fun e1 => fun e2 => (tc (rel_seq r1 (tc r2))) e1 e2 \/ e1 = e2.

Definition hx' (A:Type) (r1 r2:Rln A) : Rln A :=
  fun e1 => fun e2 => 
    rel_seq (maybe (tc r2)) (rel_seq (phx r1 (tc r2)) (maybe r1)) e1 e2. 

Definition trans (A:Type) (r:Rln A) : Prop :=
  forall x y z, r x y -> r y z -> r x z.

Lemma test : forall (A:Set) (r1 r2: Rln A) x y, (phx r1 r2 x y) = (maybe (tc (rel_seq r1 r2)) x y).
intros.
unfold phx, maybe. trivial.
Qed.

(* si r1 trans et  x r1 y (r1r2)+ z 
   alors x (r1r2)+ z *)
Lemma glue_front : forall (A:Type) (r1 r2: Rln A) (Tr1: trans r1) x y z, 
   r1 x y -> tc (rel_seq r1 r2) y z -> tc (rel_seq r1 r2) x z.
intros.
remember (rel_seq r1 r2) as r. induction H0; subst.
(* x r1 x0 r1 z r2 y donc x r1 z r2 y (par trans) donc x r1r2 y
   donc x (r1r2)+ y *)
destruct H0 as [z [? ?]].
apply trc_step. exists z; split; trivial.
apply Tr1 with x0; trivial.
(*  cas trc_ind; trivial *)
apply trc_ind with z; trivial.
apply IHtc1; trivial.
Qed.

(* si r2 trans et x (r1r2)+ y r2 z
   alors x (r1r2)+ z *)
Lemma glue_back : forall (A:Type) (r1 r2: Rln A) (Tr2: trans r2) x y z, 
   tc (rel_seq r1 r2) x y -> r2 y z ->  tc (rel_seq r1 r2) x z.
intros.
remember (rel_seq r1 r2) as r. induction H; subst.
(* x r1 a r2 y r2 z donc x r1 a r2 z (par trans) donc x r1r2 z
   donc x (r1r2)+ z *)
destruct H as [a [? ?]].
apply trc_step. exists a; split; trivial.
apply Tr2 with y; trivial.
(*  cas trc_ind; trivial *)
apply trc_ind with z0; trivial.
apply IHtc2; trivial.
Qed.

Lemma hx_trans : (*2*)
  forall (A:Type) (r1 r2:Rln A),
  trans r1 -> trans r2 ->
  trans (hx r1 r2).
Proof.
intros.
unfold trans in *; intros.
unfold hx in *.
destruct H1 as [z1 [? ?]].
destruct H2 as [z2 [? ?]].
destruct H3 as [z11 [? ?]].
destruct H4 as [z21 [? ?]].
destruct H3; destruct H4.

  exists z1; split; trivial; clear x H1.
  exists z21; split; trivial; clear z H6.
  destruct H5; destruct H2; left.
    apply trc_ind with z11; trivial; clear z1 H3.
    apply trc_ind with z2; trivial; clear z21 H4.
    apply trc_step. exists y; split; trivial.

    apply trc_ind with z11; trivial; clear z1 H3.
    apply glue_front with y; subst; trivial.

    apply trc_ind with z2; trivial; clear z21 H4.
    apply glue_back with y; subst; trivial. 

    apply trc_ind with z11; subst; trivial.

  subst. exists z1; split; trivial; clear x H1.
  destruct H2.
    exists z21; split; trivial. clear z H6. left.
    destruct H5.
      apply trc_ind with z11; trivial; clear z1 H3.
      apply trc_step. exists y; split; trivial.

      subst. apply glue_back with y; trivial.

    subst. exists z11; split. left; trivial.
    destruct H5; destruct H6; subst.
    left; apply H with z21; trivial.
    left; trivial. left; trivial. right; trivial.

  subst. destruct H5.
    exists z11; split; trivial. clear x H1.
    exists z21; split; trivial. clear z H6.
    left. destruct H2; subst.
      apply trc_ind with z2; trivial.
      apply trc_step. exists y; split; trivial.

      apply glue_front with z2; trivial.

    subst. exists z2; split.
      destruct H1; destruct H2; subst.
      left; apply H0 with y; trivial. left; trivial. 
      left; trivial. right; trivial.

      clear H1 H2. exists z21; split; trivial. left; trivial.

  subst. destruct H1; destruct H5; destruct H2; destruct H6; subst.
    exists z11; split. left; trivial.
    exists z21; split. left. apply trc_step. exists y; split; trivial.
    left; trivial.

    exists z11; split. left; trivial.
    exists z; split. left. apply trc_step. exists y; split; trivial.
    right; trivial.

    exists z11; split. left; trivial.
    exists z11; split. right; trivial.
    left; apply H with z21; trivial.

    exists z11; split. left; trivial.
    exists z11; split. right; trivial. left; trivial.

    exists z21; split. left; apply H0 with y; trivial. 
    exists z21; split. right; trivial. left; trivial. 

    exists z; split. left; apply H0 with y; trivial. exists z; split; right; trivial.

    exists z21; split. left; apply H1.
    exists z21; split. right; trivial. left; apply H4.

    exists z; split. left; apply H1.
    exists z; split; right; trivial.

    exists z11; split. right; trivial.
    exists z21; split.
      left; apply trc_step; exists y; split; [apply H3 | apply H2].
      left; apply H4.

   exists z11; split. right; trivial.
     exists z; split; [| right; trivial].
     left; apply trc_step; exists y; split; [apply H3 | apply H2].

  exists z11; split. right; trivial.
  exists z11; split. right; trivial.
  left; apply H with z21. apply H3. apply H4.

  exists z11; split. right; trivial.
  exists z11; split. right; trivial.
  left; apply H3.

  exists z21; split. left; apply H2.
  exists z21; split. right; trivial.
    left; apply H4.

  exists z; split. left; apply H2.
  exists z; split; right; trivial.

  exists z21; split; [right; trivial |].
  exists z21; split; [right; trivial |].
  left; apply H4.

  exists z; split; [right; trivial |].  
  exists z; split; right; trivial.  
Qed.

Lemma hx'_trans : (*2*)
  forall (A:Type) (r1 r2:Rln A),
  trans r1 ->
  trans (hx (tc r2) r1).
Proof.
intros.
unfold trans in *; intros.
unfold hx' in *.
destruct H0 as [z1 [? ?]].
destruct H1 as [z2 [? ?]].
destruct H2 as [z11 [? ?]].
destruct H3 as [z21 [? ?]].
destruct H2; destruct H3.

  exists z1; split; trivial; clear x H0.
  exists z21; split; trivial; clear z H5.
  destruct H4; destruct H1; left.
    apply trc_ind with z11; trivial; clear z1 H2.
    apply trc_ind with z2; trivial; clear z21 H3.
    apply trc_step. exists y; split; trivial.

    apply trc_ind with z11; trivial; clear z1 H2.
    apply glue_front with y; subst; trivial.
    intros e1 e2 e3 H12 H23.
      apply trc_ind with e2; auto. 

    apply trc_ind with z2; trivial; clear z21 H3.
    apply glue_back with y; subst; trivial.

    apply trc_ind with z11; subst; trivial.

  subst. exists z1; split; trivial; clear x H0.
  destruct H1.
    exists z21; split; trivial. clear z H5. left.
    destruct H4.
      apply trc_ind with z11; trivial; clear z1 H2.
      apply trc_step. exists y; split; trivial.

      subst. apply glue_back with y; trivial.
    subst. exists z11; split. left; trivial.
    destruct H4; destruct H5; subst.
    left; apply trc_ind with z21; auto.
    left; trivial. left; trivial. right; trivial.
   
  subst. destruct H4.
    exists z11; split; trivial. clear x H0.
    exists z21; split; trivial. clear z H5.
    left. destruct H1; subst.
      apply trc_ind with z2; trivial.
      apply trc_step. exists y; split; trivial.

      apply glue_front with z2; trivial.

    subst. 
    intros e1 e2 e3 H12 H23.
      apply trc_ind with e2; auto. 
  exists z2; split.
      destruct H0; destruct H1; subst.
      left; apply H with y; trivial. left; trivial. 
      left; trivial. right; trivial.

      clear H0 H1. exists z21; split; trivial. left; trivial.

  subst. destruct H0; destruct H4; destruct H1; destruct H5; subst.
    exists z11; split. left; trivial.
    exists z21; split. left. apply trc_step. exists y; split; trivial.
    left; trivial.

    exists z11; split. left; trivial.
    exists z; split. left. apply trc_step. exists y; split; trivial.
    right; trivial.

    exists z11; split. left; trivial.
    exists z11; split. right; trivial.
    left; apply trc_ind with z21; trivial.

    exists z11; split. left; trivial.
    exists z11; split. right; trivial. left; trivial.

    exists z21; split. left; apply H with y; trivial. 
    exists z21; split. right; trivial. left; trivial. 

    exists z; split. left; apply H with y; trivial. exists z; split; right; trivial.

    exists z21; split. left; apply H0.
    exists z21; split. right; trivial. left; apply H3.

    exists z; split. left; apply H0.
    exists z; split; right; trivial.

    exists z11; split. right; trivial.
    exists z21; split.
      left; apply trc_step; exists y; split; [apply H2 | apply H1].
      left; apply H3.

   exists z11; split. right; trivial.
     exists z; split; [| right; trivial].
     left; apply trc_step; exists y; split; [apply H2 | apply H1].

  exists z11; split. right; trivial.
  exists z11; split. right; trivial.
  left; apply trc_ind with z21. apply H2. apply H3.

  exists z11; split. right; trivial.
  exists z11; split. right; trivial.
  left; apply H2.

  exists z21; split. left; apply H1.
  exists z21; split. right; trivial.
    left; apply H3.

  exists z; split. left; apply H1.
  exists z; split; right; trivial.

  exists z21; split; [right; trivial |].
  exists z21; split; [right; trivial |].
  left; apply H3.

  exists z; split; [right; trivial |].  
  exists z; split; right; trivial.  
Qed. 

Lemma tc_dec : forall (A:Type) (r:Rln A) (x y:A),  
  tc r x y -> 
  exists z,  (r x z /\ (tc r z y \/ z = y)).
intros.
induction H.
exists y; split;trivial. right; trivial.
destruct IHtc1 as [z1 ?]. destruct H1. destruct H2.
destruct IHtc2 as [z2 ?]. destruct H3. destruct H4.
exists z1; intuition. left.
eapply trc_ind. apply H2. eapply trc_ind. apply trc_step. apply H3.
trivial.
exists z1; intuition. left.
eapply trc_ind. apply H2. apply trc_step.  rewrite <- H4. trivial.
destruct IHtc2 as [z2 ?]. destruct H3. destruct H4.
exists z1; intuition. left.
rewrite H2. eapply trc_ind. apply trc_step. apply H3. trivial.
exists z1; intuition. left.
rewrite H2. rewrite <- H4. constructor; trivial.
Qed.

Lemma tc_dec2 : forall (A:Set) (r:Rln A) (x y:A),  
  tc r x y -> 
  exists z,  ((tc r x z \/ z = x) /\ r z y).
intros.
induction H.
exists x; split;trivial. right; trivial.
destruct IHtc1 as [z1 ?]. destruct H1.
destruct IHtc2 as [z2 ?]. destruct H3. 
exists z2; intuition. left.
eapply trc_ind. apply H5. eapply trc_ind. apply trc_step. apply H2.
trivial.
left. apply trc_ind with z1; auto.
  rewrite H1; apply trc_step; auto.
left; eapply trc_ind. subst; apply trc_step. apply H2. auto.
subst; left. apply trc_step; auto.
Qed.

Lemma union_implies_hexa_path : (*1*)
  forall A (r1 r2 r: Rln A) (x y:A),
  trans r2 ->
  trans r ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r) x y)->
  (hx r2 r) x y.
Proof.
intros A r1 r2 r x y Ht2 Htr Hincl Hin.
induction Hin as [x y Hs |].
  (*step case*)
  inversion Hs as [Hhb | Hpo].
     (*hb*)
    unfold hx; unfold rel_seq. exists x; split;
      [right; trivial| exists x; split; [right; trivial| left; apply Hincl; apply Hhb]].
     (*po*)
    unfold hx; unfold rel_seq; exists y; split;
      [left; apply Hpo | exists y; split; [right; trivial|right; trivial]].
  (*ind case*)
  apply (hx_trans Ht2 Htr IHHin1 IHHin2).
Qed.

Lemma r2_left :
  forall A (r r2:Rln A) (x y z : A),
  trans r2 ->
  r2 x z ->
  tc (rel_seq r2 r) z y ->
  tc (rel_seq r2 r) x y.
Proof.
intros A r r2 x y z Ht2 Hhb_xz Htc_zy.
induction Htc_zy.
  destruct H as [z [Hhb_x0z Hpo_zy]].
  apply trc_step; exists z; split; [|apply Hpo_zy].
  eapply Ht2; [apply Hhb_xz | apply Hhb_x0z].
  apply trc_ind with z; [|apply Htc_zy2].
    apply IHHtc_zy1; apply Hhb_xz.
Qed.

Lemma r1_left :
  forall A (r r1 r2:Rln A) (x y z : A),
  trans r2 ->
  rel_incl r1 r2 ->
  r1 x z ->
  tc (rel_seq r2 r) z y ->
  tc (rel_seq r2 r) x y.
Proof.
intros A r r1 r2 x y z Ht2 Hincl Hhb_xz Htc_zy.
induction Htc_zy.
  destruct H as [z [Hhb_x0z Hpo_zy]].
  apply trc_step; exists z; split; [|apply Hpo_zy].
  eapply Ht2; [apply Hincl; apply Hhb_xz | apply Hhb_x0z].
  apply trc_ind with z; [|apply Htc_zy2].
    apply IHHtc_zy1; apply Hhb_xz.
Qed.

Lemma r1_hexa :
  forall A (r r1 r2:Rln A) (x z : A),
  ~(exists x, r2 x x) ->
  rel_incl r1 r2 ->
  trans r2 ->
  trans r ->
  r1 x z ->
  (hx r2 r) z x ->
  exists y, tc (rel_seq r2 r) y y.
Proof.
intros A r r1 r2 x z Hac2 Hincl Ht2 Htr Hhb_xz Hhx_zx.
  destruct Hhx_zx as [y [Hor_zy [y' [Hor_yy' Hor_y'x]]]].
  inversion Hor_zy as [Hpo_zy | Heq_zy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'x as [Hhb'_y'x | Heq_y'x].
    (* x -hb-> z -po-> y -tc-> y' -hb'-> x *)
    exists y; apply trc_ind with y'; [apply Htc_yy'|].
      apply trc_step; exists z; split; [| apply Hpo_zy].
       eapply Ht2; [apply Hhb'_y'x | apply Hincl; apply Hhb_xz].
    (* x -hb-> z -po-> y -tc-> y' = x *)    
   exists y; rewrite Heq_y'x in Htc_yy';
      apply trc_ind with x; [apply Htc_yy' |
        apply trc_step; exists z; split; 
          [apply Hincl; apply Hhb_xz|apply Hpo_zy]].
    (* x -hb-> z -po-> y = y' -hb'-> x *)
    exists y; apply trc_step; exists z; split; [| apply Hpo_zy].
    subst; 
      eapply Ht2; [apply Hhb'_y'x | apply Hincl; apply Hhb_xz].
    (* x -hb-> z -po-> y = y' = x *)
    exists y; subst; apply trc_step; exists z; split;
      [apply Hincl; apply Hhb_xz|apply Hpo_zy].
    (* x -hb-> z = y -tc-> y' -hb'-> x *)
    exists y'; eapply r2_left; [apply Ht2 | apply Hhb'_y'x |].
      eapply r1_left; [apply Ht2 | apply Hincl | apply Hhb_xz | subst; apply Htc_yy'].
    (* x -hb-> z = y -tc-> y' = x *)
    exists y'; subst.
      eapply r1_left; [apply Ht2 | apply Hincl | apply Hhb_xz | apply Htc_yy'].
    (* x -hb-> z = y = y' -hb'-> x *)  (*contrad hb' x x*)
      subst; assert (r2 x x) as Hhb'_xx.
        eapply Ht2; [ | apply Hhb'_y'x].
          apply Hincl; apply Hhb_xz.
      assert (exists x, r2 x x) as Hcy.
        exists x; auto.
      generalize (Hac2 Hcy); intro Htriv; 
      inversion Htriv.
    (* x -hb-> z = y = y' = x *)    
      assert (exists x, r2 x x) as Hc.
        subst; exists x; auto.
      contradiction.
Qed.

Lemma r_right :
  forall A (r r2 : Rln A) (x y z : A),
  trans r ->
  tc (rel_seq r2 r) x z ->
  r z y ->
  tc (rel_seq r2 r) x y.
Proof.
intros A r r2 x y z Htr Htc_xz Hpo_zy.
induction Htc_xz.
  destruct H as [z [Hhb'_xz Hpo_zy0]].
    apply trc_step; exists z; split; [apply Hhb'_xz | 
      eapply Htr; [apply Hpo_zy0 | apply Hpo_zy]].
apply trc_ind with z; [apply Htc_xz1 |].
  apply IHHtc_xz2; apply Hpo_zy.
Qed.

Lemma hexa_r :
  forall A (r r2 : Rln A) (x z : A),
  ~(exists x, r x x) ->
  trans r ->
  hx r2 r x z ->
  r z x ->
  exists y, tc (rel_seq r2 r) y y.
Proof.
intros A r r2 x z Hac Htr Hhx_xz Hpo_zx.
  destruct Hhx_xz as [y [Hor_xy [y' [Hor_yy' Hor_y'z]]]].
  inversion Hor_xy as [Hpo_xy | Heq_xy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'z as [Hhb'_y'z | Heq_y'z].
  (* z -po-> x -po-> y -tc-> y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_ind with y'; [apply Htc_yy' | apply trc_step].
    exists z; split; [apply Hhb'_y'z |apply Hpo_zy].
  (* z -po-> x -po-> y -tc-> y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; eapply r_right; [apply Htr | apply Htc_yy' | subst; apply Hpo_zy].
  (* z -po-> x -po-> y = y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_step; exists z; split; [subst; apply Hhb'_y'z | apply Hpo_zy].
  (* z -po-> x -po-> y = y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy; subst.
  (* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      exists z; auto.
    generalize (Hac Hcy); intro Hc; contradiction.
  (* z -po-> x = y -tc-> y' -hb'-> z *)
  exists y; apply trc_ind with y'; [apply Htc_yy' |].
    apply trc_step; exists z; split; [apply Hhb'_y'z | subst; apply Hpo_zx].
  (* z -po-> x = y -tc-> y' = z *)
  exists y; subst; eapply r_right; [apply Htr | apply Htc_yy' | apply Hpo_zx].
  (* z -po-> x = y = y' -hb'-> z *)
  exists y; subst; apply trc_step; exists z; split;
    [apply Hhb'_y'z | apply Hpo_zx].
  (* z -po-> x = y = y' = z *)
(* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      subst; exists z; auto.
  subst; generalize (Hac Hcy); intro Htriv; inversion Htriv.
Qed.

Lemma trans_tc :
  forall A (r:Rln A),
  trans r -> tc r = r.
Proof.
intros A r Ht.
generalize (ext_rel (tc r) r); intro Hext.
apply Hext; split; intro Hxy.
induction Hxy; auto.
  apply Ht with z; auto.
apply trc_step; auto.
Qed.

Lemma trans_maybe :
  forall A (r: Rln A),
  trans r -> trans (maybe r).
Proof.
intros A r Ht x y z Hxy Hyz.
inversion Hxy; inversion Hyz.
  left; apply Ht with y; auto.
  left; rewrite H0 in H; auto.
  left; rewrite <- H in H0; auto.
  right; subst; auto.
Qed.

Lemma hexa'_r :
  forall A (r r2 : Rln A) (x z : A),
  ~(exists x, r x x) ->
  trans r ->
  hx (tc r2) r x z ->
  r z x ->
  exists y, tc (rel_seq (tc r2) (maybe r)) y y.
Proof.
intros A r r2 x z Hac Htr Hhx_xz Hpo_zx.
  destruct Hhx_xz as [y [Hor_xy [y' [Hor_yy' Hor_y'z]]]].
  inversion Hor_xy as [Hpo_xy | Heq_xy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'z as [Hhb'_y'z | Heq_y'z].
  (* z -po-> x -po-> y -tc-> y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_ind with y'; [ | apply trc_step].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  apply (tc_incl Hi Htc_yy').
    exists z; split; [apply Hhb'_y'z |left; apply Hpo_zy].
  (* z -po-> x -po-> y -tc-> y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; eapply r_right; [apply trans_maybe; auto | | subst; left; apply Hpo_zy].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  subst; apply (tc_incl Hi Htc_yy').
  (* z -po-> x -po-> y = y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_step; exists z; split; [subst; apply Hhb'_y'z | left; apply Hpo_zy].
  (* z -po-> x -po-> y = y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy; subst.
  (* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      exists z; auto.
    generalize (Hac Hcy); intro Hc; contradiction.
  (* z -po-> x = y -tc-> y' -hb'-> z *)
  exists y; apply trc_ind with y'; [ |].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  apply (tc_incl Hi Htc_yy').
    apply trc_step; exists z; split; [apply Hhb'_y'z | subst; left; apply Hpo_zx].
  (* z -po-> x = y -tc-> y' = z *)
  exists y; subst; eapply r_right; [apply trans_maybe; auto | | left; apply Hpo_zx].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  apply (tc_incl Hi Htc_yy').
  (* z -po-> x = y = y' -hb'-> z *)
  exists y; subst; apply trc_step; exists z; split;
    [apply Hhb'_y'z | left; apply Hpo_zx].
  (* z -po-> x = y = y' = z *)
(* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      subst; exists z; auto.
  subst; generalize (Hac Hcy); intro Htriv; inversion Htriv.
Qed.

Lemma union_cycle_implies_seq_cycle : 
  forall A (r1 r2 r : Rln A) (x:A),
  ~(exists x, rel_union r1 r x x) ->
  ~(exists x, r x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  trans r ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r)) x x ->
  (exists y, (tc (rel_seq r2 r)) y y).
Proof.
intros A r1 r2 r x ac_u Hacr Hac2 Ht2 Htr Hincl Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      generalize (union_implies_hexa_path Ht2 Htr Hincl Htc_zx); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        eapply (r1_hexa); auto; [apply Hincl | apply Hhb_xz | apply Hp_zx].
        apply (hexa_r Hacr Htr Hp_zx Hpo_xz).
     generalize (ac_u); intro Hco.
     assert (exists x, rel_union r1 r x x) as Hcon.
       exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
     contradiction.
Qed.

Lemma union_implies_hx_path : 
  forall A (r1 r2: Rln A) (x y:A),
  trans r1 -> trans r2 ->
  (tc (rel_union r1 r2) x y)->
  hx r2 r1 x y.
Proof.
intros A r1 r2 x y Htr1 Htr2 Hin.
induction Hin.
  inversion H as [H1 | H2];
    unfold hx; unfold rel_seq; unfold maybe.
      exists y; split; [left; auto |exists y; split; right;auto].
      exists x; split; [right; auto | exists x; split; [right; auto | left; auto]].
  apply (hx_trans Htr2 Htr1 IHHin1 IHHin2).
Qed.

Lemma union_implies_hx'_path : 
  forall A (r1 r2: Rln A) (x y:A),
  trans r1 ->
  (tc (rel_union r1 r2) x y)->
  hx (tc r2) r1 x y.
Proof.
intros A r1 r2 x y Htr1 Hin.
induction Hin.
  inversion H as [H1 | H2];
    unfold hx; unfold rel_seq; unfold maybe.
      exists y; split; [left; auto |exists y; split; right;auto]. 
      exists x; split; [right; auto | exists x; split; [right; auto | left; auto]].
      apply trc_step; auto.
  apply (hx'_trans Htr1 IHHin1 IHHin2).
Qed.

Lemma seq_path_implies_union_path :
  forall A (r1 r2: Rln A) (x y:A),
  tc (rel_seq r2 r1) x y ->
  (tc (rel_union r1 r2) x y).
Proof.
intros A r1 r2 x y Hxy.
induction Hxy.
  destruct H as [z [Hxz Hzy]].
  apply trc_ind with z; apply trc_step; [right; auto | left; auto].
  apply trc_ind with z; auto.
Qed.

Lemma hx_implies_union_path : 
  forall A (r1 r2: Rln A) (x y:A),
  hx r2 r1 x y ->
  (tc (rel_union r1 r2) x y) \/ x = y.
Proof.
intros A r1 r2 x y Hin.
destruct Hin as [x0 [Hxx0 [y0 [Hx0y0 Hy0y]]]].
inversion Hxx0; [left|].
  inversion Hx0y0.
    inversion Hy0y.
      apply trc_ind with x0. 
        apply trc_step; left; auto.
        apply trc_ind with y0.
          apply seq_path_implies_union_path; auto.
          apply trc_step; right; auto.
          subst; apply trc_ind with x0.
            apply trc_step; left; auto.
            apply seq_path_implies_union_path; auto.
      subst; inversion Hy0y.
      apply trc_ind with y0; apply trc_step; [left; auto | right; auto].
      subst; apply trc_step; left; auto.

  inversion Hx0y0.
    inversion Hy0y.
      left; subst; apply trc_ind with y0.
          apply seq_path_implies_union_path; auto.
          apply trc_step; right; auto.
          subst; left; apply seq_path_implies_union_path; auto.
      subst; inversion Hy0y.
      left; apply trc_step; right; auto.
      right; auto.
Qed.

Lemma r2_hexa :
  forall A (r1 r2:Rln A) (x z : A),
  ~(exists x, r2 x x) ->
  trans r2 ->
 (*trans r1 ->*)
  r2 x z ->
  (hx r2 r1) z x ->
  exists y, tc (rel_seq r2 r1) y y.
Proof.
intros A r1 r2 x z Hac2 Ht2 (*Ht1*) Hhb_xz Hhx_zx.
  destruct Hhx_zx as [y [Hor_zy [y' [Hor_yy' Hor_y'x]]]].
  inversion Hor_zy as [Hpo_zy | Heq_zy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'x as [Hhb'_y'x | Heq_y'x].
    (* x -hb-> z -po-> y -tc-> y' -hb'-> x *)
    exists y; apply trc_ind with y'; [apply Htc_yy'|].
      apply trc_step; exists z; split; [| apply Hpo_zy].
       eapply Ht2; [apply Hhb'_y'x | apply Hhb_xz].
    (* x -hb-> z -po-> y -tc-> y' = x *)    
   exists y; rewrite Heq_y'x in Htc_yy';
      apply trc_ind with x; [apply Htc_yy' |
        apply trc_step; exists z; split; 
          [apply Hhb_xz|apply Hpo_zy]].
    (* x -hb-> z -po-> y = y' -hb'-> x *)
    exists y; apply trc_step; exists z; split; [| apply Hpo_zy].
    subst; 
      eapply Ht2; [apply Hhb'_y'x | apply Hhb_xz].
    (* x -hb-> z -po-> y = y' = x *)
    exists y; subst; apply trc_step; exists z; split;
      [apply Hhb_xz|apply Hpo_zy].
    (* x -hb-> z = y -tc-> y' -hb'-> x *)
    subst; exists y'; eapply r2_left; [apply Ht2 | apply Hhb'_y'x |].
      eapply r2_left; [apply Ht2 | apply Hhb_xz | subst; apply Htc_yy'].
    (* x -hb-> z = y -tc-> y' = x *)
    exists y'; subst.
      eapply r2_left; [apply Ht2 | apply Hhb_xz | apply Htc_yy'].
    (* x -hb-> z = y = y' -hb'-> x *)  (*contrad hb' x x*)
      subst; assert (r2 x x) as Hhb'_xx.
        eapply Ht2; [ | apply Hhb'_y'x].
          apply Hhb_xz.
      assert (exists x, r2 x x) as Hcy.
        exists x; auto.
      generalize (Hac2 Hcy); intro Htriv; 
      inversion Htriv.
    (* x -hb-> z = y = y' = x *)    
      assert (exists x, r2 x x) as Hc.
        subst; exists x; auto.
      contradiction.
Qed.

Lemma r2_hexa' :
  forall A (r1 r2:Rln A) (x z : A),
  ~(exists x, r2 x x) ->
  trans r1 ->
  r2 x z ->
  (hx (tc r2) r1) z x ->
  exists y, tc (rel_seq (tc r2) (maybe r1)) y y.
Proof.
intros A r1 r2 x z Hac2 Ht1 Hhb_xz Hhx_zx.
  destruct Hhx_zx as [y [Hor_zy [y' [Hor_yy' Hor_y'x]]]].
  inversion Hor_zy as [Hpo_zy | Heq_zy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'x as [Hhb'_y'x | Heq_y'x].
    (* x -hb-> z -po-> y -tc-> y' -hb'-> x *)
    exists y; apply trc_ind with y'; [|].
  assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
      auto. left; auto.
  apply (tc_incl Hi Htc_yy').  
      apply trc_step; exists z; split; [| left; apply Hpo_zy].
       eapply trc_ind; [apply Hhb'_y'x | left; apply Hhb_xz].
    (* x -hb-> z -po-> y -tc-> y' = x *)    
   exists y; rewrite Heq_y'x in Htc_yy';
      apply trc_ind with x; [ |
        apply trc_step; exists z; split; 
          [left; apply Hhb_xz|left; apply Hpo_zy]].
  assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
      auto. left; auto.
  apply (tc_incl Hi Htc_yy').  
    (* x -hb-> z -po-> y = y' -hb'-> x *)
    exists y; apply trc_step; exists z; split; [|left; apply Hpo_zy].
    subst; 
      eapply trc_ind; [apply Hhb'_y'x | left; apply Hhb_xz].
    (* x -hb-> z -po-> y = y' = x *)
    exists y; subst; apply trc_step; exists z; split;
      [left; apply Hhb_xz| left; apply Hpo_zy].
    (* x -hb-> z = y -tc-> y' -hb'-> x *)
    subst; exists y'; eapply r2_left; [ | apply Hhb'_y'x |].
    intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
      eapply r2_left; [ | left; apply Hhb_xz | subst].
    intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
  assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
      auto. left; auto.
  apply (tc_incl Hi Htc_yy').
    (* x -hb-> z = y -tc-> y' = x *)
    exists y'; subst.
      eapply r2_left; [ | left; apply Hhb_xz | ].
    intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
  assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
        auto. left; auto.
  apply (tc_incl Hi Htc_yy').
    (* x -hb-> z = y = y' -hb'-> x *)  (*contrad hb' x x*)
   exists y'; apply trc_step.
   exists z; split; [|subst]; auto.
   apply trc_ind with x; auto; apply trc_step; auto.
    (* x -hb-> z = y = y' = x *)    
      assert (exists x, r2 x x) as Hc.
        subst; exists x; auto.
      contradiction.
Qed.

Lemma union_cycle_implies_seq_cycle2 : 
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r2 ->
  trans r1 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq r2 r1)) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht2 Ht1 Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      generalize (union_implies_hx_path Ht1 Ht2 Htc_zx); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        apply (hexa_r Hac1 Ht1 Hp_zx Hhb_xz).
        eapply (r2_hexa); auto; [apply Hpo_xz | apply Hp_zx].
     assert (exists x, rel_union r1 r2 x x) as Hcon.
       exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
     contradiction.
Qed.

Lemma union_cycle_implies_seq_cycle3 : 
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r1 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (tc r2) (maybe r1))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht1 Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      generalize (union_implies_hx'_path Ht1 Htc_zx); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        apply (hexa'_r Hac1 Ht1 Hp_zx Hhb_xz).
        eapply (r2_hexa'); auto; [apply Hpo_xz | apply Hp_zx].
     assert (exists x, rel_union r1 r2 x x) as Hcon.
       exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
     contradiction.
Qed.

Lemma union_cycle_implies_seq_cycle4 : 
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r2 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (tc r1) (maybe r2))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht2 Hc.
rewrite union_triv in Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      generalize (union_implies_hx'_path Ht2 Htc_zx); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        apply (hexa'_r Hac2 Ht2 Hp_zx Hhb_xz).
        eapply (r2_hexa'); auto; [apply Hpo_xz | apply Hp_zx].
     assert (exists x, rel_union r1 r2 x x) as Hcon.
       exists x; rewrite Heq_zx in Hr_xz; rewrite union_triv in Hr_xz; apply Hr_xz.
     contradiction.
Qed.

Lemma union_cycle_implies_seq_cycle_fin : 
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, tc r1 x x) ->
  ~(exists x, tc r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (tc r2) (tc r1))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      assert (trans (tc r1)) as Ht1.
        intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
      assert (trans (tc r2)) as Ht2.
        intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
      assert (tc (rel_union (tc r1) (tc r2)) z x) as Htc_zx'.
        generalize Htc_zx; apply tc_incl; intros e1 e2 H12;
        inversion H12; [left | right]; apply trc_step; auto.
      generalize (union_implies_hx_path Ht1 Ht2 Htc_zx'); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        assert (tc r1 x z) as Hhb_xz'.
          apply trc_step; auto.
        apply (hexa_r Hac1 Ht1 Hp_zx Hhb_xz').
        eapply (r2_hexa); auto.
        apply trc_step; apply Hpo_xz. apply Hp_zx.
     assert (exists x, rel_union r1 r2 x x) as Hcon.
       exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
     contradiction.
Qed.

Lemma seq_path_implies_inv_seq_path :
  forall A (r1 r2 : Rln A) (x y:A),
  (tc (rel_seq r1 r2)) x y ->
  (exists e1, exists e2, r1 x e1 /\ (maybe (tc (rel_seq r2 r1))) e1 e2 /\ r2 e2 y).
Proof.
intros A r1 r2 x y Hxy.
induction Hxy.
  destruct H as [e [Hxe Hey]]; exists e; exists e; split; auto; split; auto.
    right; auto.
  destruct IHHxy1 as [e [e' [Hxe [Hee' He'z]]]];
  destruct IHHxy2 as [e1 [e2 [Hz1 [H12 H2y]]]].
    exists e; exists e2; split; auto; split; auto.
    inversion Hee'.
    left; apply trc_ind with e'; auto.
      inversion H12.
        apply trc_ind with e1; auto.
          apply trc_step; exists z; auto.
        apply trc_step; exists z; split; auto; subst; auto.
    subst.
      inversion H12.
        left; apply trc_ind with e1; auto.
          apply trc_step; exists z; auto.
        left; apply trc_step; exists z; split; auto; subst; auto.
Qed.

Lemma seq_cycle_implies_inv_seq_cycle :
  forall A (r1 r2 : Rln A) (x:A),
  (tc (rel_seq r1 r2)) x x ->
  (exists y, (tc (rel_seq r2 r1)) y y).
Proof.
intros A r1 r2 x Hx.
generalize (seq_path_implies_inv_seq_path Hx); intros [e [e' [Hxe [Hee' He'y]]]].
  inversion Hee'.
    exists e'; apply trc_ind with e; auto.
      apply trc_step; exists x; split; auto.
    subst; exists e'; apply trc_step; exists x; split; auto.
Qed.

Lemma union_cycle_implies_seq_cycle5 : 
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r2 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (maybe r2) (tc r1))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht2 Hc.
generalize (union_cycle_implies_seq_cycle4 Hac1 Hac2 Hu Ht2 Hc); intros [y Hy].
apply (seq_cycle_implies_inv_seq_cycle Hy).
Qed.

Lemma union_cycle_implies_seq_cycle6 : 
  forall A (r1 r2 r : Rln A) (x:A),
  ~(exists x, rel_union r1 r x x) ->
  ~(exists x, r x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r)) x x ->
  (exists y, (tc (rel_seq (tc r) (maybe r2) )) y y).
Proof.
intros A r1 r2 r x ac_u Hacr Hac2 Ht2 Hincl Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      assert (tc (rel_union r2 r) z x) as Hzx'.
        apply tc_incl with (rel_union r1 r); auto.
          intros e1 e2 H12; inversion H12; auto.
            left; apply Hincl; auto. right; auto.
            
      generalize (union_implies_hx'_path Ht2 Hzx'); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        assert (r2 x z) as Hxz'.
          apply Hincl; auto.
        apply (hexa'_r Hac2 Ht2 Hp_zx Hxz').
        eapply (r2_hexa'); auto; [apply Hpo_xz | apply Hp_zx].
     generalize (ac_u); intro Hco.
     assert (exists x, rel_union r1 r x x) as Hcon.
       exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
     contradiction.
Qed.

Lemma union_cycle_implies_seq_cycle' : 
  forall A (r1 r2 r : Rln A) (x:A),
  ~(exists x, rel_union r1 r x x) ->
  ~(exists x, r x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r)) x x ->
  (exists y, (tc (rel_seq (maybe r2) (tc r))) y y).
Proof.
intros A r1 r2 r x Hacu Hacr Hac2 Ht2 Hincl Hc.
generalize (union_cycle_implies_seq_cycle6 Hacu Hacr Hac2 Ht2 Hincl Hc); intros [y Hy].
apply (seq_cycle_implies_inv_seq_cycle Hy).
Qed.

Lemma seq_in_maybe_sure_maybe :
  forall A (r1 r2: Rln A) (x y:A),
  tc (rel_seq r2 r1) x y ->
  tc (rel_seq (maybe r2) (rel_seq r1 (maybe r2))) x y.
Proof.
intros A r1 r2 x y Hxy.
induction Hxy.
  destruct H as [z [Hxz Hzy]]; apply trc_step.
  exists z; split; [left; auto | exists y; split; [auto | right; auto]].
  apply trc_ind with z; auto.
Qed.

Lemma union_cycle_implies_seq_seq_cycle : 
  forall A (r1 r2: Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  trans r1 -> 
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (maybe r2) (rel_seq r1 (maybe r2)))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Ht2 Ht1 Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      generalize (union_implies_hx_path Ht1 Ht2 Htc_zx); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        generalize (hexa_r Hac1 Ht1 Hp_zx Hhb_xz); intros [y Hy].
        exists y; apply seq_in_maybe_sure_maybe; auto.
        generalize (r2_hexa Hac2 Ht2 Hpo_xz Hp_zx); intros [y Hy].
        exists y; apply seq_in_maybe_sure_maybe; auto.
  rewrite Heq_zx in Hr_xz; inversion Hr_xz.
  assert (exists x, r1 x x) as H1.
    exists x; auto.
  contradiction.
  assert (exists x, r2 x x) as H2.
    exists x; auto.
  contradiction.
Qed.

Lemma union_union_implies_union_hx_path : 
  forall A (r1 r2 r : Rln A) (x y:A),
  (tc (rel_union r (rel_union r1 r2)) x y)->
  tc (rel_union r (hx r2 r1)) x y.
Proof.
intros A r1 r2 r x y Hin.
induction Hin.
  inversion H as [Hr | H12]; apply trc_step.
    left; auto.
    inversion H12 as [H1 | H2];
    unfold hx; unfold rel_seq; unfold maybe; right.
      exists y; split; [left; auto |exists y; split; right;auto].
      exists x; split; [right; auto | exists x; split; [right; auto | left; auto]].
  apply trc_ind with z; auto.
Qed.

Definition rel_sub (A:Set) (r1 r2 : Rln A) :=
  fun e1 e2 => r2 e1 e2 /\ not (r1 e1 e2).
Definition mrel (A:Set) (b:bool) (r:Rln A) :=
  if b then r else (fun e1 => fun e2 => False).

Lemma irr_trans_ac :
  forall A (r : Rln A),
  trans r ->
  ~ (exists x, r x x) ->
  acyclic r.
Proof.
unfold acyclic;
intros A r Ht Hc y Hy.
rewrite (trans_tc Ht) in Hy.
assert (exists x, r x x) as Hco.
  exists y; auto.
contradiction.
Qed.

Lemma lin_implies_part :
  forall A (r:Rln A) (s:set A),
  linear_strict_order r s ->
  partial_order r s.
Proof.
intros A r s Hlin.
destruct_lin Hlin; split; auto.
Qed.

Lemma convoluted_u :
  forall A (r1 r2 : Rln A),
  rel_incl (rel_union (rel_union (rel_seq r1 r2) (rel_seq r2 r1)) 
    (rel_union r1 r2)) 
      (tc (rel_union r1 r2)).
Proof.
intros A r1 r2 x y Hxy.
  inversion Hxy as [Hs | Hu].
    inversion Hs as [H12 | H21].
      destruct H12 as [z [H1 H2]]; apply trc_ind with z; 
      apply trc_step; [left | right]; auto.
      destruct H21 as [z [H2 H1]]; apply trc_ind with z; 
      apply trc_step; [right | left]; auto.
    apply trc_step; auto.
Qed.

Lemma irrefl_equiv :
  forall A (r1 r2 : Rln A),
  (~exists x, rel_seq r1 r2 x x) <-> 
  (~exists x, rel_seq r2 r1 x x).
Proof.
intros A r1 r2; split; intros Hn [x [e [H1 H2]]]; apply Hn;
  exists e; exists x; split; auto.
Qed.

End BasicRel.

Unset Implicit Arguments.