Require Import CRIS.

From Stdlib Require Import MSetList.

Require Import Basic.
Require Import DataStructure.
Require Import Loc.
Require Import Language.
Require Import Event.

Set Implicit Arguments.


Module BoolMap (A: UsualDecidableType).
  Definition t := A.t -> bool.
  Module AFun := UsualFun A.

  Definition bot: t := fun _ => false.
  Definition top: t := fun _ => true.

  Definition le (lhs rhs: t): Prop :=
    forall a (LHS: lhs a = true), rhs a = true.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. auto.
  Qed.
  Next Obligation.
    ii. auto.
  Qed.
  #[global] Hint Resolve le_PreOrder_obligation_1: core.
  #[global] Hint Resolve le_PreOrder_obligation_2: core.

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    extensionality a.
    specialize (LR a). specialize (RL a).
    destruct (l a) eqn:L, (r a) eqn:R; eauto.
    exploit LR; eauto.
  Qed.

  Lemma bot_spec bm: le bot bm.
  Proof.
    ii. ss.
  Qed.

  Lemma top_spec bm: le bm top.
  Proof.
    ii. ss.
  Qed.

  Definition disjoint (x y: t): Prop :=
    forall a (GET1: x a = true) (GET2: y a = true), False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eauto.
  Qed.

  Lemma bot_disjoint bm: disjoint bot bm.
  Proof.
    ii. ss.
  Qed.

  Definition finite (bm: t): Prop :=
    exists dom,
    forall a (GET: bm a = true),
      List.In a dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ss.
  Qed.


  Variant add (bm1: t) (a: A.t) (bm2: t): Prop :=
  | add_intro
      (GET: bm1 a = false)
      (BM2: bm2 = AFun.add a true bm1)
  .
  #[global] Hint Constructors add: core.

  Variant remove (bm1: t) (a: A.t) (bm2: t): Prop :=
  | remove_intro
      (GET: bm1 a = true)
      (BM2: bm2 = AFun.add a false bm1)
  .
  #[global] Hint Constructors remove: core.


  Lemma add_o
        bm2 bm1 a l
        (ADD: add bm1 a bm2):
    bm2 l = if A.eq_dec l a then true else bm1 l.
  Proof.
    inv ADD. unfold AFun.add. ss.
  Qed.

  Lemma add_get0
        bm1 a bm2
        (ADD: add bm1 a bm2):
    (<<GET1: bm1 a = false>>) /\
    (<<GET2: bm2 a = true>>).
  Proof.
    inv ADD. split; ss.
    unfold AFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        bm1 a bm2 l
        (ADD: add bm1 a bm2)
        (GET: bm1 l = true):
    bm2 l = true.
  Proof.
    inv ADD. unfold AFun.add. condtac; ss.
  Qed.

  Lemma add_le
        bm1 a bm2
        (ADD: add bm1 a bm2):
    le bm1 bm2.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
  Qed.

  Lemma le_add
        a x1 x2 y1 y2
        (LE1: le x1 y1)
        (ADDX: add x1 a x2)
        (ADDY: add y1 a y2):
    le x2 y2.
  Proof.
    ii. revert LHS.
    inv ADDX. inv ADDY.
    unfold AFun.add.
    condtac; ss; eauto.
  Qed.

  Lemma add_finite
        bm1 a bm2
        (ADD: add bm1 a bm2)
        (FINITE: finite bm1):
    finite bm2.
  Proof.
    inv ADD. inv FINITE.
    exists (a :: x). unfold AFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma add_exists
        bm1 a
        (GET: bm1 a = false):
    <<ADD: exists bm2, add bm1 a bm2>>.
  Proof.
    eauto.
  Qed.

  Lemma le_add_exists
        a x1 y1 y2
        (LE1: le x1 y1)
        (ADDY: add y1 a y2):
    exists x2, <<ADDX: add x1 a x2>> /\ <<LE2: le x2 y2>>.
  Proof.
    exploit (add_exists x1 a).
    { inv ADDY. destruct (x1 a) eqn:GETX; ss. exploit LE1; eauto. }
    i. des. esplits; eauto. eapply le_add; eauto.
  Qed.

  Lemma remove_o
        bm2 bm1 a l
        (REMOVE: remove bm1 a bm2):
    bm2 l = if A.eq_dec l a then false else bm1 l.
  Proof.
    inv REMOVE. unfold AFun.add. ss.
  Qed.

  Lemma remove_get0
        bm1 a bm2
        (REMOVE: remove bm1 a bm2):
    (<<GET1: bm1 a = true>>) /\
    (<<GET2: bm2 a = false>>).
  Proof.
    inv REMOVE. split; ss.
    unfold AFun.add. condtac; ss.
  Qed.

  Lemma remove_get1
        bm1 a bm2 l
        (REMOVE: remove bm1 a bm2)
        (GET: bm1 l = true):
    (<<A: l = a>>) \/
    (<<GET2: bm2 l = true>>).
  Proof.
    inv REMOVE. unfold AFun.add. condtac; auto.
  Qed.

  Lemma remove_le
        bm1 a bm2
        (REMOVE: remove bm1 a bm2):
    le bm2 bm1.
  Proof.
    ii. revert LHS.
    erewrite remove_o; eauto. condtac; ss.
  Qed.

  Lemma le_remove
        a x1 x2 y1 y2
        (LE1: le x1 y1)
        (REMOVEX: remove x1 a x2)
        (REMOVEY: remove y1 a y2):
    le x2 y2.
  Proof.
    ii. revert LHS.
    inv REMOVEX. inv REMOVEY.
    unfold AFun.add.
    condtac; ss; eauto.
  Qed.

  Lemma remove_finite
        bm1 a bm2
        (REMOVE: remove bm1 a bm2)
        (FINITE: finite bm1):
    finite bm2.
  Proof.
    inv REMOVE. inv FINITE.
    exists x. unfold AFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma remove_exists
        bm1 a
        (GET: bm1 a = true):
    <<REMOVE: exists bm2, remove bm1 a bm2>>.
  Proof.
    eauto.
  Qed.

  Lemma le_remove_exists
        a x1 y1 y2
        (LE1: le x1 y1)
        (ADDY: remove y1 a y2):
    (exists x2, <<REMOVEX: remove x1 a x2>> /\ <<LE2: le x2 y2>>) \/
    (<<LE2: le x1 y2>>).
  Proof.
    destruct (x1 a) eqn:GETX.
    - exploit (remove_exists x1 a); eauto.
      i. des. left. esplits; eauto. eapply le_remove; eauto.
    - right. ii. erewrite remove_o; eauto. condtac; eauto. congruence.
  Qed.

  Definition minus (gbm bm: t): t :=
    fun a => andb (gbm a) (negb (bm a)).

  Lemma minus_true_spec gbm bm a:
    minus gbm bm a = true <->
    gbm a = true /\ bm a = false.
  Proof.
    unfold minus. split; i.
    - rewrite Bool.andb_true_iff in H. des. split; ss.
      destruct (bm a); ss.
    - des. rewrite H H0. ss.
  Qed.

  Lemma add_minus
        gbm1 gbm2
        bm1 bm2
        a
        (GADD: add gbm1 a gbm2)
        (ADD: add bm1 a bm2):
    minus gbm1 bm1 = minus gbm2 bm2.
  Proof.
    extensionality l. unfold minus.
    inv GADD. inv ADD.
    unfold AFun.add. condtac; ss. subst.
    rewrite GET GET0. ss.
  Qed.

  Lemma remove_minus
        gbm1 gbm2
        bm1 bm2
        a
        (GREMOVE: remove gbm1 a gbm2)
        (REMOVE: remove bm1 a bm2):
    minus gbm1 bm1 = minus gbm2 bm2.
  Proof.
    extensionality l. unfold minus.
    inv GREMOVE. inv REMOVE.
    unfold AFun.add. condtac; ss. subst.
    rewrite GET GET0. ss.
  Qed.

  Lemma minus_bot bm:
    minus bm bot = bm.
  Proof.
    extensionality l. unfold minus. ss. destruct (bm l); ss.
  Qed.

  (* reorder *)

  Lemma reorder_add_add
        bm0
        a1 bm1
        a2 bm2
        (ADD1: add bm0 a1 bm1)
        (ADD2: add bm1 a2 bm2):
    exists bm1',
      (<<ADD1: add bm0 a2 bm1'>>) /\
      (<<ADD2: add bm1' a1 bm2>>).
  Proof.
    inv ADD1. inv ADD2.
    unfold AFun.add in GET0. des_ifs.
    esplits; eauto. econs.
    - unfold AFun.add. condtac; ss. congruence.
    - apply AFun.add_add. ss.
  Qed.

  Lemma reorder_add_remove
        bm0
        a1 bm1
        a2 bm2
        (ADD1: add bm0 a1 bm1)
        (REMOVE2: remove bm1 a2 bm2):
    (<<A: a1 = a2>>) /\ (<<BM: bm0 = bm2>>) \/
    (<<A: a1 <> a2>>) /\
    exists bm1',
      (<<REMOVE1: remove bm0 a2 bm1'>>) /\
      (<<ADD2: add bm1' a1 bm2>>).
  Proof.
    inv ADD1. inv REMOVE2.
    unfold AFun.add in GET0. des_ifs.
    - left. splits; ss.
      extensionality a.
      unfold AFun.add. condtac; subst; ss.
      unfold AFun.find. condtac; ss.
    - right. splits; try congruence.
      esplits; eauto. econs.
      + unfold AFun.add. condtac; ss.
      + apply AFun.add_add. ss.
  Qed.

  Lemma reorder_remove_add
        bm0
        a1 bm1
        a2 bm2
        (REMOVE1: remove bm0 a1 bm1)
        (ADD2: add bm1 a2 bm2):
    (<<A: a1 = a2>>) /\ (<<BM: bm0 = bm2>>) \/
    (<<A: a1 <> a2>>) /\
    exists bm1',
      (<<ADD1: add bm0 a2 bm1'>>) /\
      (<<REMOVE2: remove bm1' a1 bm2>>).
  Proof.
    inv REMOVE1. inv ADD2.
    unfold AFun.add in GET0. des_ifs.
    - left. splits; ss.
      extensionality a.
      unfold AFun.add. condtac; subst; ss.
      unfold AFun.find. condtac; ss.
    - right. splits; try congruence.
      esplits; eauto. econs.
      + unfold AFun.add. condtac; ss.
      + apply AFun.add_add. ss.
  Qed.

  Lemma reorder_remove_remove
        bm0
        a1 bm1
        a2 bm2
        (REMOVE1: remove bm0 a1 bm1)
        (REMOVE2: remove bm1 a2 bm2):
    exists bm1',
      (<<REMOVE1: remove bm0 a2 bm1'>>) /\
      (<<REMOVE2: remove bm1' a1 bm2>>).
  Proof.
    inv REMOVE1. inv REMOVE2.
    unfold AFun.add in GET0. des_ifs.
    esplits; eauto. econs.
    - unfold AFun.add. condtac; ss. congruence.
    - apply AFun.add_add. ss.
  Qed.

  Lemma le_minus_le
        bm1 gbm1 bm2 gbm2
        (LE: le bm2 bm1)
        (WF1: le bm1 gbm1)
        (MINUS: minus gbm2 bm2 = minus gbm1 bm1):
    le gbm2 gbm1.
  Proof.
    ii. destruct (bm2 a) eqn: LBM2; eauto.
    eapply equal_f with a in MINUS. unfold minus in *. rewrite LHS in MINUS. rewrite LBM2 in MINUS.
    destruct (bm1 a) eqn:LBM1; eauto. destruct (gbm1 a); ss.
  Qed.
End BoolMap.

