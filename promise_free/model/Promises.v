Require Import CRIS.

Require Import MSetList.

Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Language.
Require Import Event.
Require Import Ordering.

Require Import BoolMap.

Set Implicit Arguments.

Module UsualPromises (A: UsualDecidableType).
  Include (BoolMap A).

  Variant promise (prm1 gprm1: t) (a: A.t) (prm2 gprm2: t): Prop :=
  | promise_intro
      (ADD: add prm1 a prm2)
      (GADD: add gprm1 a gprm2)
  .
  #[global] Hint Constructors promise: core.

  Variant fulfill (prm1 gprm1: t) (a: A.t) (ord: Ordering.t) (prm2 gprm2: t): Prop :=
  | fulfill_refl
      (PROMISES: prm2 = prm1)
      (GPROMISES: gprm2 = gprm1)
  | fulfill_remove
      (ORD: Ordering.le ord Ordering.na)
      (REMOVE: remove prm1 a prm2)
      (GREMOVE: remove gprm1 a gprm2)
  .
  #[global] Hint Constructors fulfill: core.

  Variant sfulfill (prm1 gprm1: t) (a: A.t) (prm2 gprm2: t): Prop :=
  | sfulfill_refl
      (PROMISES: prm2 = prm1)
      (GPROMISES: gprm2 = gprm1)
      (NOPRM: prm1 a = false)
  | sfulfill_remove
(REMOVE: remove prm1 a prm2)
      (GREMOVE: remove gprm1 a gprm2)
  .
  #[global] Hint Constructors sfulfill: core.

  Inductive fulfills (prm1 gprm1: t) (a: list A.t) (ord: Ordering.t) (prm2 gprm2: t): Prop :=
  | fulfill_empty
      (EMPTY: a = [])
      (PROMISES: prm2 = prm1)
      (GPROMISES: gprm2 = gprm1)
  | fulfill_cons h t prm' gprm'
      (CONS: a = h::t)
      (FULFILL: fulfill prm1 gprm1 h ord prm' gprm')
      (FULFILLS: fulfills prm' gprm' t ord prm2 gprm2)
  .

  Lemma promise_le
        prm1 gprm1 a prm2 gprm2
        (PROMISE: promise prm1 gprm1 a prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    inv PROMISE. eauto using le_add.
  Qed.

  Lemma fulfill_le
        prm1 gprm1 a ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 a ord prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    inv FULFILL; eauto using le_remove.
  Qed.

  Lemma sfulfill_le
        prm1 gprm1 a prm2 gprm2
        (FULFILL: sfulfill prm1 gprm1 a prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    inv FULFILL; eauto using le_remove.
  Qed.

  Lemma fulfills_le
        prm1 gprm1 l ord prm2 gprm2
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    induction FULFILLS; subst; ss. eapply IHFULFILLS. eapply fulfill_le; eauto.
  Qed.

  Lemma fulfill_le2
        prm1 gprm1 a ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 a ord prm2 gprm2):
    le prm2 prm1 /\ le gprm2 gprm1.
  Proof.
    inv FULFILL; ss. split; eauto using remove_le.
  Qed.
  
  Lemma sfulfill_le2
        prm1 gprm1 a prm2 gprm2
        (FULFILL: sfulfill prm1 gprm1 a prm2 gprm2):
    le prm2 prm1 /\ le gprm2 gprm1.
  Proof.
    inv FULFILL; ss. split; eauto using remove_le.
  Qed.
  
  Lemma fulfills_le2
        prm1 gprm1 l ord prm2 gprm2
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2):
    le prm2 prm1 /\ le gprm2 gprm1.
  Proof.
    induction FULFILLS; subst; ss.
    exploit fulfill_le2; eauto. i. des. split; eauto.
  Qed.
  
  Lemma promise_disjoint
        prm1 gprm1 a prm2 gprm2
        ctx
        (PROMISE: promise prm1 gprm1 a prm2 gprm2)
        (LE_CTX: le ctx gprm1)
        (DISJOINT: disjoint prm1 ctx):
    (<<DISJOINT: disjoint prm2 ctx>>) /\
    (<<LE_CTX: le ctx gprm2>>).
  Proof.
    inv PROMISE. inv ADD. inv GADD. splits; ii.
    - revert GET1. unfold AFun.add.
      condtac; ss; subst; eauto.
    - unfold AFun.add. condtac; ss; eauto.
  Qed.

  Lemma fulfill_disjoint
        prm1 gprm1 a ord prm2 gprm2
        ctx
        (FULFILL: fulfill prm1 gprm1 a ord prm2 gprm2)
        (LE_CTX: le ctx gprm1)
        (DISJOINT: disjoint prm1 ctx):
    (<<DISJOINT: disjoint prm2 ctx>>) /\
    (<<LE_CTX: le ctx gprm2>>).
  Proof.
    inv FULFILL; auto. inv REMOVE. inv GREMOVE. splits; ii.
    - revert GET1. unfold AFun.add.
      condtac; ss; subst; eauto.
    - unfold AFun.add. condtac; ss; subst; eauto.
  Qed.

  Lemma sfulfill_disjoint
        prm1 gprm1 a prm2 gprm2
        ctx
        (FULFILL: sfulfill prm1 gprm1 a prm2 gprm2)
        (LE_CTX: le ctx gprm1)
        (DISJOINT: disjoint prm1 ctx):
    (<<DISJOINT: disjoint prm2 ctx>>) /\
    (<<LE_CTX: le ctx gprm2>>).
  Proof.
    inv FULFILL; auto. inv REMOVE. inv GREMOVE. splits; ii.
    - revert GET1. unfold AFun.add.
      condtac; ss; subst; eauto.
    - unfold AFun.add. condtac; ss; subst; eauto.
  Qed.

  Lemma fulfills_disjoint
        prm1 gprm1 l ord prm2 gprm2
        ctx
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2)
        (LE_CTX: le ctx gprm1)
        (DISJOINT: disjoint prm1 ctx):
    (<<DISJOINT: disjoint prm2 ctx>>) /\
    (<<LE_CTX: le ctx gprm2>>).
  Proof.
    induction FULFILLS; subst; auto.
    exploit fulfill_disjoint; eauto. i. des.
    eapply IHFULFILLS; eauto.
  Qed.

  Lemma promise_finite
        prm1 gprm1 a prm2 gprm2
        (PROMISE: promise prm1 gprm1 a prm2 gprm2)
        (FINITE1: finite prm1):
    finite prm2.
  Proof.
    inv PROMISE. eauto using add_finite.
  Qed.

  Lemma fulfill_finite
        prm1 gprm1 a ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 a ord prm2 gprm2)
        (FINITE1: finite prm1):
    finite prm2.
  Proof.
    inv FULFILL; auto. eauto using remove_finite.
  Qed.

  Lemma sfulfill_finite
        prm1 gprm1 a prm2 gprm2
        (FULFILL: sfulfill prm1 gprm1 a prm2 gprm2)
        (FINITE1: finite prm1):
    finite prm2.
  Proof.
    inv FULFILL; auto. eauto using remove_finite.
  Qed.

  Lemma fulfills_finite
        prm1 gprm1 l ord prm2 gprm2
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2)
        (FINITE1: finite prm1):
    finite prm2.
  Proof.
    induction FULFILLS; subst; auto.
    eapply IHFULFILLS. eapply fulfill_finite; eauto.
  Qed.

  Lemma promise_minus
        prm1 gprm1 a prm2 gprm2
        (PROMISE: promise prm1 gprm1 a prm2 gprm2):
    minus gprm1 prm1 = minus gprm2 prm2.
  Proof.
    inv PROMISE. eauto using add_minus.
  Qed.

  Lemma fulfill_minus
        prm1 gprm1 a ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 a ord prm2 gprm2):
    minus gprm1 prm1 = minus gprm2 prm2.
  Proof.
    inv FULFILL; ss. eauto using remove_minus.
  Qed.

  Lemma sfulfill_minus
        prm1 gprm1 a prm2 gprm2
        (FULFILL: sfulfill prm1 gprm1 a prm2 gprm2):
    minus gprm1 prm1 = minus gprm2 prm2.
  Proof.
    inv FULFILL; ss. eauto using remove_minus.
  Qed.

  Lemma fulfills_minus
        prm1 gprm1 l ord prm2 gprm2
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2):
    minus gprm1 prm1 = minus gprm2 prm2.
  Proof.
    induction FULFILLS; subst; auto.
    erewrite fulfill_minus; eauto.
  Qed.

  Lemma promise_minus_inv
        prm1 gprm1 a prm2 gprm2
        (PROMISE: promise prm1 gprm1 a prm2 gprm2):
    minus prm1 gprm1 = minus prm2 gprm2.
  Proof.
    inv PROMISE. eauto using add_minus.
  Qed.

  Lemma fulfill_minus_inv
        prm1 gprm1 a ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 a ord prm2 gprm2):
    minus prm1 gprm1 = minus prm2 gprm2.
  Proof.
    inv FULFILL; ss. eauto using remove_minus.
  Qed.

  Lemma fulfills_minus_inv
        prm1 gprm1 l ord prm2 gprm2
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2):
    minus prm1 gprm1 = minus prm2 gprm2.
  Proof.
    induction FULFILLS; subst; auto.
    erewrite fulfill_minus_inv; eauto.
  Qed.

  Lemma fulfill_not_eq
        prm1 gprm1 a1 ord prm2 gprm2 a2
        (FULFILL: fulfill prm1 gprm1 a1 ord prm2 gprm2)
        (NOTEQ: a1 <> a2):
    prm2 a2 = prm1 a2 /\ gprm2 a2 = gprm1 a2.
  Proof.
    inv FULFILL; eauto. inv REMOVE. inv GREMOVE.
    change (AFun.add a1 false prm1 a2) with (AFun.find a2 (AFun.add a1 false prm1)).
    change (AFun.add a1 false gprm1 a2) with (AFun.find a2 (AFun.add a1 false gprm1)).
    rewrite AFun.add_spec_neq; eauto. rewrite AFun.add_spec_neq; eauto.
  Qed.
  
  Lemma sfulfill_not_eq
        prm1 gprm1 a1 prm2 gprm2 a2
        (FULFILL: sfulfill prm1 gprm1 a1 prm2 gprm2)
        (NOTEQ: a1 <> a2):
    prm2 a2 = prm1 a2 /\ gprm2 a2 = gprm1 a2.
  Proof.
    inv FULFILL; eauto. inv REMOVE. inv GREMOVE.
    change (AFun.add a1 false prm1 a2) with (AFun.find a2 (AFun.add a1 false prm1)).
    change (AFun.add a1 false gprm1 a2) with (AFun.find a2 (AFun.add a1 false gprm1)).
    rewrite AFun.add_spec_neq; eauto. rewrite AFun.add_spec_neq; eauto.
  Qed.        
  
  Lemma fulfills_inv_not_in
        prm1 gprm1 l ord prm2 gprm2 loc
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2)
        (IN: ~ List.In loc l):
    (prm2 loc = prm1 loc /\ gprm2 loc = gprm1 loc).
  Proof.
    induction FULFILLS; subst; ss.
    eapply not_or_and in IN. des.
    exploit IHFULFILLS; eauto. i. des. rewrite x0. rewrite x1.
    inv FULFILL; ss. inv REMOVE. inv GREMOVE.
    change (AFun.add h false prm1 loc) with (AFun.find loc (AFun.add h false prm1)).
    change (AFun.add h false gprm1 loc) with (AFun.find loc (AFun.add h false gprm1)).
    rewrite AFun.add_spec_neq; eauto.
    rewrite AFun.add_spec_neq; eauto.
  Qed.
  
  Lemma fulfills_inv_in
        prm1 gprm1 l ord prm2 gprm2 loc
        (FULFILLS: fulfills prm1 gprm1 l ord prm2 gprm2)
        (IN: List.In loc l):
    (prm2 loc = prm1 loc /\ gprm2 loc = gprm1 loc) \/
    (prm1 loc = true /\ prm2 loc = false /\ gprm1 loc = true /\ gprm2 loc = false).
  Proof.
    induction FULFILLS; try by (subst; inv IN). subst.
    destruct (classic (loc = h)).
    - inv FULFILL.
      + destruct (classic (In h t0)).
        * exploit IHFULFILLS; eauto.
        * exploit fulfills_inv_not_in; eauto.
      + destruct (classic (In h t0)).
        * right. exploit IHFULFILLS; eauto. i. des.
          -- rewrite x0. rewrite x1.
             inv REMOVE. inv GREMOVE. esplits; eauto; eapply AFun.add_spec_eq.
          -- inv REMOVE.
             change (AFun.add h false prm1 h) with (AFun.find h (AFun.add h false prm1)) in x0.
             rewrite AFun.add_spec_eq in x0. congruence.
        * right. exploit fulfills_inv_not_in; eauto. i. des. rewrite x0. rewrite x0 in IHFULFILLS. rewrite x1. rewrite x1 in IHFULFILLS.
          inv REMOVE. inv GREMOVE. esplits; eauto; eapply AFun.add_spec_eq.
    - inv IN; ss. exploit fulfill_not_eq; eauto. i. des. rewrite <- x0. rewrite <- x1.
      eapply IHFULFILLS; eauto.
  Qed.

  (* reorder *)

  Lemma reorder_promise_promise
        prm0 gprm0
        a1 prm1 gprm1
        a2 prm2 gprm2
        (PROMISE1: promise prm0 gprm0 a1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 a2 prm2 gprm2):
    exists prm1' gprm1',
      (<<PROMISE1: promise prm0 gprm0 a2 prm1' gprm1'>>) /\
      (<<PROMISE2: promise prm1' gprm1' a1 prm2 gprm2>>).
  Proof.
    inv PROMISE1. inv PROMISE2.
    exploit reorder_add_add; try exact ADD; eauto. i. des.
    exploit reorder_add_add; try exact GADD; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma reorder_fulfill_promise
        prm0 gprm0
        a1 ord1 prm1 gprm1
        a2 prm2 gprm2
        (FULFILL1: fulfill prm0 gprm0 a1 ord1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 a2 prm2 gprm2)
        (A: a1 <> a2):
    exists prm1' gprm1',
      (<<PROMISE1: promise prm0 gprm0 a2 prm1' gprm1'>>) /\
      (<<FULFILL2: fulfill prm1' gprm1' a1 ord1 prm2 gprm2>>).
  Proof.
    inv FULFILL1; [esplits; eauto|]. inv PROMISE2.
    exploit reorder_remove_add; try exact REMOVE; eauto. i. des; try congruence.
    exploit reorder_remove_add; try exact GREMOVE; eauto. i. des; try congruence.
    esplits; eauto.
  Qed.

  Lemma reorder_sfulfill_promise
        prm0 gprm0
        a1 prm1 gprm1
        a2 prm2 gprm2
        (FULFILL1: sfulfill prm0 gprm0 a1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 a2 prm2 gprm2)
        (A: a1 <> a2):
    exists prm1' gprm1',
      (<<PROMISE1: promise prm0 gprm0 a2 prm1' gprm1'>>) /\
      (<<FULFILL2: sfulfill prm1' gprm1' a1 prm2 gprm2>>).
  Proof.
    inv FULFILL1; inv PROMISE2.
    - esplits; eauto. econs 1; ss. erewrite add_o; eauto. condtac; ss.
    - exploit reorder_remove_add; try exact REMOVE; eauto. i. des; try congruence.
      exploit reorder_remove_add; try exact GREMOVE; eauto. i. des; try congruence.
      esplits; eauto.
  Qed.

  Lemma reorder_fulfills_promise
        prm0 gprm0
        la1 ord1 prm1 gprm1
        a2 prm2 gprm2
        (FULFILL1: fulfills prm0 gprm0 la1 ord1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 a2 prm2 gprm2)
        (A: ~ List.In a2 la1):
    exists prm1' gprm1',
      (<<PROMISE1: promise prm0 gprm0 a2 prm1' gprm1'>>) /\
      (<<FULFILL2: fulfills prm1' gprm1' la1 ord1 prm2 gprm2>>).
  Proof.
    exploit fulfills_inv_not_in; eauto. i. des.
    inv PROMISE2. inv ADD. inv GADD. esplits. 
    - econs; econs; eauto.
    - clear x0 x1 GET GET0. induction FULFILL1.
      + subst. econs; eauto. 
      + subst. eapply not_in_cons in A. des.
        econs 2; try eapply IHFULFILL1; eauto. inv FULFILL; eauto.
        econs 2; eauto.
        * inv REMOVE. econs.
          -- replace (AFun.add a2 true prm1 h) with (AFun.find h (AFun.add a2 true prm1)); ss.
             rewrite AFun.add_spec_neq; eauto.
          -- eapply AFun.add_add; eauto.
        * inv GREMOVE. econs.
          -- replace (AFun.add a2 true gprm1 h) with (AFun.find h (AFun.add a2 true gprm1)); ss.
             rewrite AFun.add_spec_neq; eauto.
          -- eapply AFun.add_add; eauto.
  Qed.

  Lemma reorder_fulfill_promise_same
        prm0 gprm0
        loc ord1 prm1 gprm1
        prm2 gprm2
        (FULFILL1: fulfill prm0 gprm0 loc ord1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 loc prm2 gprm2):
    exists prm1' gprm1',
      (<<PROMISE1: sflib.__guard__ (prm1' = prm0 /\ gprm1' = gprm0 \/
                              promise prm0 gprm0 loc prm1' gprm1')>>) /\
      (<<FULFILL2: fulfill prm1' gprm1' loc ord1 prm2 gprm2>>).
  Proof.
    inv FULFILL1.
    { esplits; eauto. right. ss. }
    inv PROMISE2. esplits; [left; eauto|]. econs.
    - extensionality l.
      erewrite (@add_o prm2); eauto.
      erewrite (@remove_o prm1); eauto.
      condtac; ss. subst. inv REMOVE. ss.
    - extensionality l.
      erewrite (@add_o gprm2); eauto.
      erewrite (@remove_o gprm1); eauto.
      condtac; ss. subst. inv GREMOVE. ss.
  Qed.

  Lemma reorder_sfulfill_promise_same
        prm0 gprm0
        loc prm1 gprm1
        prm2 gprm2
        (FULFILL1: sfulfill prm0 gprm0 loc prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 loc prm2 gprm2):
    promise prm0 gprm0 loc prm2 gprm2 \/ (prm2 = prm0 /\ gprm2 = gprm0).
  Proof.
    inv FULFILL1; inv PROMISE2.
    - left. ss.
    - right. exploit reorder_remove_add; try exact ADD; eauto. i. des; try congruence.
      exploit reorder_remove_add; try exact GADD; eauto. i. des; try congruence.
      esplits; eauto.
  Qed.

  Lemma reorder_fulfills_promise_same
        prm0 gprm0
        loc la ord1 prm1 gprm1
        prm2 gprm2
        (FULFILL1: fulfills prm0 gprm0 la ord1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 loc prm2 gprm2)
        (LOC: List.In loc la)
        (NODUP: List.NoDup la):
    exists prm1' gprm1',
      (<<PROMISE1: sflib.__guard__ (prm1' = prm0 /\ gprm1' = gprm0 \/
                              promise prm0 gprm0 loc prm1' gprm1')>>) /\
      (<<FULFILL2: fulfills prm1' gprm1' la ord1 prm2 gprm2>>).
  Proof.
    generalize dependent gprm2. generalize dependent prm2.
    generalize dependent gprm1. generalize dependent prm1.
    generalize dependent gprm0. generalize dependent prm0.
    induction la; i.
    - inv FULFILL1; ss.
    - destruct (classic (loc = a)).
      + inv NODUP. inv LOC; ss. inv FULFILL1; ss. clarify.
        exploit reorder_fulfills_promise; eauto. i. des.
        exploit reorder_fulfill_promise_same; eauto. i. des.
        esplits; eauto. econs 2; eauto.
      + inv LOC; ss. inv NODUP. inv FULFILL1; ss. clarify.
        exploit IHla; eauto. i. des. unfold sflib.__guard__ in *. des.
        * subst. esplits; eauto. econs 2; eauto.
        * exploit reorder_fulfill_promise; eauto. i. des.
          esplits; eauto. econs 2; eauto.
  Qed.

  Lemma reorder_promise_fulfill
        prm0 gprm0
        a1 prm1 gprm1
        a2 ord2 prm2 gprm2
        (PROMISE1: promise prm0 gprm0 a1 prm1 gprm1)
        (FULFILL2: fulfill prm1 gprm1 a2 ord2 prm2 gprm2)
        (A: a1 <> a2):
    exists prm1' gprm1',
      (<<FULFILL1: fulfill prm0 gprm0 a2 ord2 prm1' gprm1'>>) /\
      (<<PROMISE2: promise prm1' gprm1' a1 prm2 gprm2>>).
  Proof.
    inv FULFILL2; [esplits; eauto|]. inv PROMISE1.
    exploit reorder_add_remove; try exact ADD; eauto. i. des; try congruence.
    exploit reorder_add_remove; try exact GADD; eauto. i. des; try congruence.
    esplits; [econs 2|]; eauto.
  Qed.

  Lemma reorder_promise_sfulfill
        prm0 gprm0
        a1 prm1 gprm1
        a2 prm2 gprm2
        (PROMISE1: promise prm0 gprm0 a1 prm1 gprm1)
        (FULFILL2: sfulfill prm1 gprm1 a2 prm2 gprm2)
        (A: a1 <> a2):
    exists prm1' gprm1',
      (<<FULFILL1: sfulfill prm0 gprm0 a2 prm1' gprm1'>>) /\
      (<<PROMISE2: promise prm1' gprm1' a1 prm2 gprm2>>).
  Proof.
    inv FULFILL2; inv PROMISE1.
    - esplits; eauto. econs 1; ss. revert NOPRM. erewrite add_o; eauto. condtac; ss.
    - exploit reorder_add_remove; try exact ADD; eauto. i. des; try congruence.
      exploit reorder_add_remove; try exact GADD; eauto. i. des; try congruence.
      esplits; eauto.
  Qed.

  Lemma reorder_promise_sfulfill_same
        prm0 gprm0
        a prm1 gprm1
        prm2 gprm2
        (PROMISE1: promise prm0 gprm0 a prm1 gprm1)
        (FULFILL2: sfulfill prm1 gprm1 a prm2 gprm2):
    prm2 = prm0 /\ gprm2 = gprm0.
  Proof.
    inv FULFILL2; inv PROMISE1.
    - exploit add_get0; try exact ADD. i. des. congruence.
    - exploit reorder_add_remove; try exact ADD; eauto. i. des; try congruence.
      exploit reorder_add_remove; try exact GADD; eauto. i. des; try congruence.
      esplits; eauto.
  Qed.

  Lemma reorder_fulfill_fulfill
        prm0 gprm0
        a1 ord1 prm1 gprm1
        a2 ord2 prm2 gprm2
        (FULFILL1: fulfill prm0 gprm0 a1 ord1 prm1 gprm1)
        (FULFILL2: fulfill prm1 gprm1 a2 ord2 prm2 gprm2)
        (A: a1 <> a2):
    exists prm1' gprm1',
      (<<FULFILL1: fulfill prm0 gprm0 a2 ord2 prm1' gprm1'>>) /\
      (<<FULFILL2: fulfill prm1' gprm1' a1 ord1 prm2 gprm2>>).
  Proof.
    inv FULFILL1; [esplits; eauto|].
    inv FULFILL2; [esplits; eauto|].
    exploit reorder_remove_remove; try exact REMOVE; eauto. i. des; try congruence.
    exploit reorder_remove_remove; try exact GREMOVE; eauto. i. des; try congruence.
    esplits; [econs 2|]; eauto.
  Qed.

  Lemma reorder_sfulfill_sfulfill
        prm0 gprm0
        a1 prm1 gprm1
        a2 prm2 gprm2
        (FULFILL1: sfulfill prm0 gprm0 a1 prm1 gprm1)
        (FULFILL2: sfulfill prm1 gprm1 a2 prm2 gprm2)
        (A: a1 <> a2):
    exists prm1' gprm1',
      (<<FULFILL1: sfulfill prm0 gprm0 a2 prm1' gprm1'>>) /\
      (<<FULFILL2: sfulfill prm1' gprm1' a1 prm2 gprm2>>).
  Proof.
    inv FULFILL1; inv FULFILL2; ss.
    - esplits; eauto.
    - esplits; eauto. econs; eauto. erewrite remove_o; eauto. condtac; ss.
    - esplits; eauto. econs; eauto. revert NOPRM. erewrite remove_o; eauto. condtac; ss. congruence.
    - exploit reorder_remove_remove; try exact REMOVE; eauto. i. des; try congruence.
      exploit reorder_remove_remove; try exact GREMOVE; eauto. i. des; try congruence.
      esplits; eauto.
  Qed.
  
  Lemma disjoint_minus_le_r
        bm1 bm2 gbm
        (LE1: le bm1 gbm)
        (LE2: le bm2 gbm)
        (DISJOINT: disjoint bm1 bm2):
    le bm2 (minus gbm bm1).
  Proof.
    ii. exploit LE2; eauto. i.
    unfold minus. rewrite x0. s.
    destruct (bm1 a) eqn:GET1; ss.
    exploit DISJOINT; eauto.
  Qed.

  Lemma sim_fulfill
        prm1_src gprm1_src
        prm1_tgt gprm1_tgt loc ord prm2_tgt gprm2_tgt
        (PROMISES: le prm1_src prm1_tgt)
        (GPROMISES: minus gprm1_src prm1_src = minus gprm1_tgt prm1_tgt)
        (LE_SRC: le prm1_src gprm1_src)
        (FULFILL_TGT: fulfill prm1_tgt gprm1_tgt loc ord prm2_tgt gprm2_tgt):
    exists prm2_src gprm2_src,
        (<<FULFILL_SRC: fulfill prm1_src gprm1_src loc ord prm2_src gprm2_src>>) /\
        (<<PROMISES: le prm2_src prm2_tgt>>) /\
        (<<GPROMISES: minus gprm2_src prm2_src = minus gprm2_tgt prm2_tgt>>).
  Proof.
    inv FULFILL_TGT.
    { esplits; [econs 1|..]; eauto. }
    exploit remove_get0; try exact REMOVE. i. des.
    exploit remove_get0; try exact GREMOVE. i. des.
    destruct (prm1_src loc) eqn:GET_SRC.
    - destruct (gprm1_src loc) eqn:GGET_SRC; cycle 1.
      { exploit LE_SRC; eauto. congruence. }
      exploit remove_exists; try exact GET_SRC. i. des.
      exploit remove_exists; try exact GGET_SRC. i. des.
      esplits; [econs 2|..]; eauto using le_remove.
      erewrite <- remove_minus; try exact x0; try exact x1.
      rewrite GPROMISES. eauto using remove_minus.
    - destruct (gprm1_src loc) eqn:GGET_SRC.
      { unfold minus in *.
        apply equal_f with (x:=loc) in GPROMISES.
        rewrite GET1 GET0 GET_SRC GGET_SRC in GPROMISES. ss.
      }
      esplits; [econs 1|..]; eauto.
      + ii. exploit PROMISES; eauto. i.
        inv REMOVE. unfold AFun.add. condtac; ss. congruence.
      + extensionality x. unfold minus in *.
        inv REMOVE. inv GREMOVE. unfold AFun.add. condtac; ss.
        * subst. rewrite GET_SRC GGET_SRC. ss.
        * eapply equal_f in GPROMISES. rewrite GPROMISES. ss.
          Unshelve. exact x.
  Qed.

  Lemma sim_sfulfill
        prm1_src gprm1_src
        prm1_tgt gprm1_tgt loc prm2_tgt gprm2_tgt
        (PROMISES: le prm1_src prm1_tgt)
        (GPROMISES: minus gprm1_src prm1_src = minus gprm1_tgt prm1_tgt)
        (LE_SRC: le prm1_src gprm1_src)
        (FULFILL_TGT: sfulfill prm1_tgt gprm1_tgt loc prm2_tgt gprm2_tgt):
    exists prm2_src gprm2_src,
        (<<FULFILL_SRC: sfulfill prm1_src gprm1_src loc prm2_src gprm2_src>>) /\
        (<<PROMISES: le prm2_src prm2_tgt>>) /\
        (<<GPROMISES: minus gprm2_src prm2_src = minus gprm2_tgt prm2_tgt>>).
  Proof.
    inv FULFILL_TGT.
    { esplits; [econs 1|..]; eauto. destruct (prm1_src loc) eqn:PRM_SRC; ss.
      exploit PROMISES; eauto.
    }
    exploit remove_get0; try exact REMOVE. i. des.
    exploit remove_get0; try exact GREMOVE. i. des.
    destruct (prm1_src loc) eqn:GET_SRC.
    - destruct (gprm1_src loc) eqn:GGET_SRC; cycle 1.
      { exploit LE_SRC; eauto. congruence. }
      exploit remove_exists; try exact GET_SRC. i. des.
      exploit remove_exists; try exact GGET_SRC. i. des.
      esplits; [econs 2|..]; eauto using le_remove.
      erewrite <- remove_minus; try exact x0; try exact x1.
      rewrite GPROMISES. eauto using remove_minus.
    - destruct (gprm1_src loc) eqn:GGET_SRC.
      { unfold minus in *.
        eapply equal_f with (x:=loc) in GPROMISES.
        rewrite GET1 GET0 GET_SRC GGET_SRC in GPROMISES. ss.
      }
      esplits; [econs 1|..]; eauto.
      + ii. exploit PROMISES; eauto. i.
        inv REMOVE. unfold AFun.add. condtac; ss. congruence.
      + extensionality x. unfold minus in *.
        inv REMOVE. inv GREMOVE. unfold AFun.add. condtac; ss.
        * subst. rewrite GET_SRC GGET_SRC. ss.
        * eapply equal_f in GPROMISES. rewrite GPROMISES. ss.
          Unshelve. exact x.
  Qed.

  Lemma sim_fulfills
        prm1_src gprm1_src
        prm1_tgt gprm1_tgt l ord prm2_tgt gprm2_tgt
        (PROMISES: le prm1_src prm1_tgt)
        (GPROMISES: minus gprm1_src prm1_src = minus gprm1_tgt prm1_tgt)
        (LE_SRC: le prm1_src gprm1_src)
        (FULFILLS_TGT: fulfills prm1_tgt gprm1_tgt l ord prm2_tgt gprm2_tgt):
    exists prm2_src gprm2_src,
        (<<FULFILLS_SRC: fulfills prm1_src gprm1_src l ord prm2_src gprm2_src>>) /\
        (<<PROMISES: le prm2_src prm2_tgt>>) /\
        (<<GPROMISES: minus gprm2_src prm2_src = minus gprm2_tgt prm2_tgt>>).
  Proof.
    revert PROMISES GPROMISES LE_SRC FULFILLS_TGT.
    revert prm1_src gprm1_src prm1_tgt gprm1_tgt prm2_tgt gprm2_tgt. induction l; i.
    { inv FULFILLS_TGT; ss. esplits; [econs; ss|..]; eauto. }
    inv FULFILLS_TGT; ss.
    exploit sim_fulfill; try exact FULFILL; eauto. i. des.
    exploit IHl; try exact FULFILLS; eauto.
    { eapply fulfill_le; eauto. }
    i. des. esplits; eauto. econs 2; eauto.
  Qed.

  Lemma fulfill_bot
        a ord gprm1 prm2 gprm2
        (FULFILL: fulfill bot gprm1 a ord prm2 gprm2):
    prm2 = bot /\ gprm2 = gprm1.
  Proof.
    inv FULFILL; ss. inv REMOVE; ss.
  Qed.

  Lemma fulfill_bot_inv
        a ord prm1 prm2 gprm2
        (FULFILL: fulfill prm1 bot a ord prm2 gprm2):
    prm2 = prm1 /\ gprm2 = bot.
  Proof.
    inv FULFILL; ss. inv GREMOVE; ss.
  Qed.

  Lemma sfulfill_bot
        a gprm1 prm2 gprm2
        (FULFILL: sfulfill bot gprm1 a prm2 gprm2):
    prm2 = bot /\ gprm2 = gprm1.
  Proof.
    inv FULFILL; ss. inv REMOVE; ss.
  Qed.

  Lemma sfulfill_bot_inv
        a prm1 prm2 gprm2
        (FULFILL: sfulfill prm1 bot a prm2 gprm2):
    prm2 = prm1 /\ gprm2 = bot.
  Proof.
    inv FULFILL; ss. inv GREMOVE; ss.
  Qed.

  Lemma fulfills_from_bot
        l ord prm:
        fulfills bot prm l ord bot prm.
  Proof.
    induction l; ss.
    - econs; ss.
    - econs 2; eauto.
  Qed.

  Lemma fulfills_bot
        l ord gprm1 prm2 gprm2
        (FULFILLS: fulfills bot gprm1 l ord prm2 gprm2):
    prm2 = bot /\ gprm2 = gprm1.
  Proof.
    generalize dependent gprm2. revert prm2 gprm1. induction l; i.
    - inv FULFILLS; ss.
    - inv FULFILLS; ss.
      exploit fulfill_bot; eauto. i. des. subst.
      eapply IHl. eauto.
  Qed.

  Lemma fulfills_bot_inv
        l ord prm1 prm2 gprm2
        (FULFILLS: fulfills prm1 bot l ord prm2 gprm2):
    prm2 = prm1 /\ gprm2 = bot.
  Proof.
    generalize dependent gprm2. revert prm1 prm2. induction l; i.
    - inv FULFILLS; ss.
    - inv FULFILLS; ss.
      exploit fulfill_bot_inv; eauto. i. des. subst.
      eapply IHl. eauto.    
  Qed.

  Lemma fulfills_in
    a l prm1 gprm1 prm2 gprm2
    (FULFILLS: fulfills prm1 gprm1 l Ordering.na prm2 gprm2)
    (PROMISED1: prm1 a = true)
    (PROMISED2: prm2 a = false):
    List.In a l.
  Proof.
    induction FULFILLS; subst; try congruence.
    destruct (A.eq_dec a h); subst; ss; eauto.
    right. eapply IHFULFILLS; eauto.
    inv FULFILL; ss. erewrite remove_o; eauto. condtac; ss.
  Qed.

  Lemma fulfills_refl prm1 gprm1 l:
    fulfills prm1 gprm1 l Ordering.na prm1 gprm1.
  Proof.
    induction l.
    { esplits. econs 1; ss. }
    econs 2; eauto.
  Qed.

  Lemma fulfills_exists prm1 gprm1 l:
    exists prm2 gprm2, fulfills prm1 gprm1 l Ordering.na prm2 gprm2.
  Proof.
    induction l.
    { esplits. econs 1; ss. }
    des. esplits. econs 2; eauto.
  Qed.

  Lemma fulfill_exists2 prm1 gprm1 loc
        (LE: prm1 loc = gprm1 loc):
    exists prm2 gprm2,
      (<<EXIST: fulfill prm1 gprm1 loc Ordering.na prm2 gprm2>>) /\
      (<<FULFILLED: prm2 loc = false /\ gprm2 loc = false>>).
  Proof.
    destruct (prm1 loc) eqn:LPRM.
    - esplits.
      + econs 2; eauto.
      + unfold AFun.add. condtac; ss.
      + unfold AFun.add. condtac; ss.
    - esplits; eauto.
  Qed.

  Lemma fulfills_exists2 prm1 gprm1 l
        (LE: forall loc, List.In loc l -> prm1 loc = gprm1 loc):
    exists prm2 gprm2,
      (<<EXIST: fulfills prm1 gprm1 l Ordering.na prm2 gprm2>>) /\
      (<<FULFILLED: forall loc, List.In loc l -> prm2 loc = false /\ gprm2 loc = false>>).
  Proof.
    revert prm1 gprm1 LE. induction l; i.
    { esplits; econs; eauto; ss. }
    destruct (prm1 a) eqn:LPRM.
    - exploit fulfill_exists2.
      { eapply LE. econs; eauto. }
      i. des.
      exploit (IHl prm2 gprm2).
      { i. inv EXIST; try (by eapply LE; econs 2; eauto). inv REMOVE. inv GREMOVE.
        unfold AFun.add. condtac; ss. eapply LE. eauto.
      }
      i. des.
      esplits.
      + econs 2; eauto.
      + i. inv H; eauto. exploit fulfills_le2; eauto. i. des. split.
        * destruct (prm0 loc) eqn:E; eauto. eapply x0 in E. congruence.
        * destruct (gprm0 loc) eqn:E; eauto. eapply x1 in E.
          rewrite LE in LPRM. rewrite E in FULFILLED0. eauto. econs; eauto.
    - exploit IHl.
      { i. eapply LE. econs 2. eauto. }
      i. des. esplits.
      + econs 2; eauto.
      + i. inv H; eauto. exploit fulfills_le2; eauto. i. des. split.
        * destruct (prm2 loc) eqn:E; eauto. eapply x0 in E. congruence.
        * destruct (gprm2 loc) eqn:E; eauto. eapply x1 in E.
          rewrite LE in LPRM; eauto. econs; eauto.
  Qed.

  Lemma sfulfill_exists prm1 gprm1 l
    (LE: le prm1 gprm1):
    exists prm2 gprm2, sfulfill prm1 gprm1 l prm2 gprm2.
  Proof.
    destruct (prm1 l) eqn:LPRM; esplits.
    { econs 2; eauto. }
    econs 1; eauto.
  Qed.
End UsualPromises.

Module Promises := UsualPromises Loc.
Module FreePromises := UsualPromises TBid.

