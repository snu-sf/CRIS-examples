Require Import CRIS.common.CRIS.

From CRIS.promise_free.lib Require Import
  Basic Loc Val DataStructure DenseOrder Event.

From CRIS.promise_free.model Require Import Time View.

Set Implicit Arguments.


Module Message.
  Variant t :=
    | message (val: Val.t) (released: View.t) (na: bool)
    | reserve
  .

  Definition elt (val: Val.t): t := message val View.bot true.

  Variant le: t -> t -> Prop :=
    | le_message
        val1 released1 na1
        val2 released2 na2
        (VAL: Val.le val2 val1)
        (RELEASED: View.le released1 released2)
        (NA: implb na2 na1):
      le (message val1 released1 na1) (message val2 released2 na2)
    | le_reserve:
      le reserve reserve
  .
  #[global] Hint Constructors le: core.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss. econs; try refl. destruct na; ss.
  Qed.
  Next Obligation.
    ii. inv H; inv H0; ss. econs; try by (etrans; eauto).
    destruct na1, na2, na3; ss.
  Qed.
End Message.


Module Cell.
  Module Raw.
    Definition t := DOMap.t (Time.t * Message.t).

    Variant wf (cell:t): Prop :=
    | wf_intro
        (VOLUME: forall from to msg
                   (GET: DOMap.find to cell = Some (from, msg)),
            Time.lt from to)
        (DISJOINT: forall to1 to2 from1 from2 msg1 msg2
                     (GET1: DOMap.find to1 cell = Some (from1, msg1))
                     (GET2: DOMap.find to2 cell = Some (from2, msg2))
                     (NEQ: to1 <> to2),
            Interval.disjoint (from1, to1) (from2, to2))
    .
    #[global] Hint Constructors wf: core.

    Definition bot: t := DOMap.empty _.

    Lemma bot_wf: wf bot.
    Proof.
      econs; i.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET1. inv GET1.
    Qed.

    Definition singleton (from to:Time.t) (msg:Message.t): t :=
      DOMap.singleton to (from, msg).

    Lemma singleton_wf
          from to msg
          (LT: Time.lt from to):
      wf (singleton from to msg).
    Proof.
      unfold singleton. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
    Qed.

    Definition init (val: Val.t): t :=
      DOMap.singleton Time.init (Time.bot, Message.elt val).

    Lemma init_wf val: wf (init val).
    Proof.
      unfold init. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. econs.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
    Qed.

    Lemma find_mem_ub
          from to msg cell
          (WF: wf cell)
          (FIND: DOMap.find to cell = Some (from, msg)):
      Interval.mem (from, to) to.
    Proof.
      inv WF. exploit VOLUME; eauto. i.
      econs; eauto. refl.
    Qed.

    Variant add (cell1:t) (from to:Time.t) (msg:Message.t) (cell2:t): Prop :=
    | add_intro
        (DISJOINT: forall to2 from2 msg2
                          (GET2: DOMap.find to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TS: Time.lt from to)
        (CELL2: cell2 = DOMap.add to (from, msg) cell1):
        add cell1 from to msg cell2.
    #[global] Hint Constructors add: core.

    Lemma add_o
          cell2 cell1 from to msg
          t
          (ADD: add cell1 from to msg cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, msg)
      else DOMap.find t cell1.
    Proof.
      inv ADD. rewrite DOMap.gsspec.
      repeat condtac; auto; congruence.
    Qed.

    Lemma add_wf
          cell1 from to msg cell2
          (ADD: add cell1 from to msg cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply VOLUME; eauto.
      - revert GET1 GET2.
        erewrite (add_o to1); eauto.
        erewrite (add_o to2); eauto.
        repeat condtac; s; i.
        + inv GET1. 
        + inv GET1. inv ADD. hexploit DISJOINT0; eauto.
        + inv GET2. inv ADD. symmetry. hexploit DISJOINT0; eauto.
        + eapply DISJOINT; eauto.
    Qed.

    Variant remove (cell1:t) (from to:Time.t) (msg:Message.t) (cell2:t): Prop :=
    | remove_intro
        (GET: DOMap.find to cell1 = Some (from, msg))
        (CELL2: cell2 = DOMap.remove to cell1)
    .
    #[global] Hint Constructors remove: core.

    Lemma remove_o
          cell2 cell1 from to msg
          t
          (REMOVE: remove cell1 from to msg cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then None
      else DOMap.find t cell1.
    Proof.
      inv REMOVE. rewrite DOMap.grspec.
      repeat condtac; auto; congruence.
    Qed.

    Lemma remove_wf
          cell1 from to msg cell2
          (REMOVE: remove cell1 from to msg cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite remove_o; eauto. condtac; try congruence.
        i. eapply VOLUME; eauto.
      - revert GET1 GET2.
        erewrite (remove_o to1); eauto.
        erewrite (remove_o to2); eauto.
        repeat condtac; repeat subst; try congruence; i.
        eapply DISJOINT; eauto.
    Qed.
  End Raw.

  Structure t := mk {
    raw :> Raw.t;
    WF: Raw.wf raw;
  }.

  Definition get (ts:Time.t) (cell:t): option (Time.t * Message.t) :=
    DOMap.find ts (raw cell).

  Lemma ext
        (lhs rhs:t)
        (EXT: forall ts, get ts lhs = get ts rhs):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    assert (raw0 = raw1).
    { apply DOMap.eq_leibniz. ii. apply EXT. }
    subst raw1. f_equal. apply proof_irrelevance.
  Qed.

  Lemma get_ts
        to cell from msg
        (GET: get to cell = Some (from, msg)):
    Time.lt from to.
  Proof.
    destruct cell. unfold get in *. ss.
    inv WF0. exploit VOLUME; eauto.
  Qed.

  Lemma get_disjoint
        f1 f2 t1 t2 msg1 msg2 cell
        (GET1: get t1 cell = Some (f1, msg1))
        (GET2: get t2 cell = Some (f2, msg2)):
    (t1 = t2 /\ f1 = f2 /\ msg1 = msg2) \/
    Interval.disjoint (f1, t1) (f2, t2).
  Proof.
    destruct (Time.eq_dec t1 t2).
    { subst. rewrite GET1 in GET2. inv GET2. auto. }
    unfold get in *. unfold Cell.get in *.
    destruct cell; ss. inv WF0.
    hexploit DISJOINT; [exact GET1|exact GET2|..]; eauto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg
      (LHS: get to lhs = Some (from, msg)),
      get to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Definition bot: t := mk Raw.bot_wf.

  Definition init val: t := mk (Raw.init_wf val).

  Lemma bot_get ts: get ts bot = None.
  Proof. unfold get, bot, Raw.bot. s. apply DOMap.gempty. Qed.

  Lemma bot_le cell: le bot cell.
  Proof. ii. rewrite bot_get in LHS. congruence. Qed.

  Lemma init_get val to:
    get to (init val) =
    if Time.eq_dec to Time.init
    then Some (Time.bot, Message.elt val)
    else None.
  Proof.
    unfold get, init, Raw.init. ss.
    condtac; ss; subst; eauto.
    rewrite DOMap.singleton_neq; ss.
  Qed.

  Lemma finite cell:
    exists dom,
    forall from to msg (GET: get to cell = Some (from, msg)),
      List.In to dom.
  Proof.
    exists (List.map (fun e => (fst e)) (DOMap.elements (Cell.raw cell))). i.
    exploit DOMap.elements_correct; eauto. i.
    eapply in_prod; eauto.
  Qed.

  Definition singleton (from to: Time.t) (msg: Message.t) (LT: Time.lt from to): t :=
    mk (Raw.singleton_wf msg LT).

  Lemma singleton_get
        from to msg t
        (LT: Time.lt from to):
    get t (singleton msg LT) =
    if Time.eq_dec t to
    then Some (from, msg)
    else None.
  Proof.
    unfold get, singleton, Raw.singleton. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition add (cell1:t) (from to:Time.t) (msg: Message.t) (cell2:t): Prop :=
    Raw.add cell1 from to msg cell2.

  Definition remove (cell1:t) (from to:Time.t) (msg: Message.t) (cell2:t): Prop :=
    Raw.remove cell1 from to msg cell2.

  Definition max_ts (cell:t): Time.t :=
    DOMap.max_key (raw cell).

  Lemma max_ts_spec
        ts from msg cell
        (GET: get ts cell = Some (from, msg)):
    <<GET: exists from msg, get (max_ts cell) cell = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts cell)>>.
  Proof.
    unfold get in GET.
    generalize (DOMap.max_key_spec (Cell.raw cell)). i. des. splits; eauto.
    - destruct (DOMap.find
                  (DOMap.max_key (Cell.raw cell))
                  (Cell.raw cell)) as [[]|]eqn:X.
      + esplits; eauto.
      + exfalso. apply FIND with (k':=ts); eauto. rewrite GET. congruence.
    - apply MAX. rewrite GET. auto.
  Qed.

  Lemma max_ts_singleton from to msg LT :
    max_ts (@singleton from to msg LT) = to.
  Proof.
    hexploit (@singleton_get from to msg to); des_ifs; intros Hget.
    hexploit max_ts_spec; eauto; i; des.
    rewrite singleton_get in GET; des_ifs; ss.
    Unshelve. ss.
  Qed.

  (* Lemmas on add *)

  Lemma add_o
        cell2 cell1 from to msg
        t
        (ADD: add cell1 from to msg cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, msg)
    else get t cell1.
  Proof. apply Raw.add_o. auto. Qed.

  (* ADDITIONAL *)
  Lemma add_le
        cell2 cell1 from to msg
        (ADD: add cell1 from to msg cell2):
    Cell.le cell1 cell2.
  Proof.
    intros ????GET; erewrite add_o; eauto; des_ifs; ss.
    inv ADD. hexploit DISJOINT; eauto.
    intros FAL; exfalso; apply (FAL to); ss; eauto using Interval.mem_ub, get_ts.
  Qed.

  Lemma le_add_le
        cell0 cell1 from to msg cell2 cell3
        (LE : le cell0 cell1)
        (ADD0 : add cell0 from to msg cell2)
        (ADD1 : add cell1 from to msg cell3) :
    le cell2 cell3.
  Proof.
    intros ???; erewrite add_o; eauto; des_if.
    { by subst; intros INV; inv INV; erewrite add_o; eauto; des_ifs; done. }
    { by intros GET%LE; eapply add_le; eauto. }
  Qed.

  (* Lemma add_trans_1
        cell0 from0 to0 msg0 cell1 from1 to1 msg1 cell2
        (ADD0 : add cell0 from0 to0 msg0 cell1)
        (ADD1 : add cell1 from1 to1 msg1 cell2) :
      add cell0 from1 to1 msg1 cell2.
  Proof.
    inv ADD0; inv ADD1.
    econs; eauto.
    { intros; eapply DISJOINT0; eauto.
      rewrite CELL2 DOMap.gso //.
      ii; clarify.
      eapply (DISJOINT to0 from2 msg2 GET2 to0); ss.
      { eapply Interval.mem_ub; ss. }
      { eapply Interval.mem_ub; ss. eapply get_ts; done. }
    }
    rewrite CELL0; ss.
     *)

  Lemma add_exists
        cell1 from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to):
    exists cell2, add cell1 from to msg cell2.
  Proof.
    destruct cell1. eexists (mk _). econs; s; eauto.
    Unshelve.
    eapply Raw.add_wf; eauto.
  Qed.

  Lemma add_exists_max_ts
        cell1 to msg
        (TO: Time.lt (max_ts cell1) to):
    exists cell2, add cell1 (max_ts cell1) to msg cell2.
  Proof.
    apply add_exists; auto. i.
    exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    assert (H1: Time.le x (max_ts cell1)).
    { etrans; [apply TO1 | apply MAX]. }
    eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        cell1' cell1 from to msg cell2
        (LE: le cell1' cell1)
        (ADD: add cell1 from to msg cell2):
    exists cell2', add cell1' from to msg cell2'.
  Proof.
    inv ADD. apply add_exists; auto. i.
    eapply DISJOINT. eauto.
  Qed.

  Lemma add_get0
        cell1 from1 to1 msg1 cell2
        (ADD: add cell1 from1 to1 msg1 cell2):
    <<GET: get to1 cell1 = None>> /\
    <<GET: get to1 cell2 = Some (from1, msg1)>>.
  Proof.
    inv ADD. unfold get. splits.
    - destruct (DOMap.find to1 (raw cell1)) as [[]|] eqn:X; auto.
      exfalso. exploit DISJOINT; eauto.
      + apply Interval.mem_ub. auto.
      + apply Interval.mem_ub.
        destruct (Cell.WF cell1). exploit VOLUME; eauto.
    - rewrite CELL2 DOMap.gsspec. condtac; ss.
  Qed.

  Lemma add_get1
        cell1 from to msg cell2
        f t m
        (ADD: add cell1 from to msg cell2)
        (GET1: get t cell1 = Some (f, m)):
    get t cell2 = Some (f, m).
  Proof.
    erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congruence.
  Qed.

  Lemma add_max_ts
        cell1 to msg cell2
        f t m
        (ADD: add cell1 (max_ts cell1) to msg cell2)
        (INHABITED: get t cell1 = Some (f, m)):
    max_ts cell2 = to.
  Proof.
    exploit add_get1; eauto. i. des.
    exploit max_ts_spec; eauto. i. des.
    revert GET. erewrite add_o; eauto. condtac; auto. i.
    apply TimeFacts.antisym.
    - left. eapply TimeFacts.le_lt_lt.
      + eapply max_ts_spec. eauto.
      + inv ADD. auto.
    - eapply max_ts_spec. erewrite add_o; eauto. condtac; ss.
  Qed.

  (* lemmas on remove *)

  Lemma remove_o
        cell2 cell1 from to msg
        t
        (REMOVE: remove cell1 from to msg cell2):
    get t cell2 =
    if Time.eq_dec t to
    then None
    else get t cell1.
  Proof.
    eapply Raw.remove_o. eauto.
  Qed.

  Lemma remove_exists
        cell1 from to msg
        (GET: get to cell1 = Some (from, msg)):
    exists cell2, remove cell1 from to msg cell2.
  Proof.
    eexists (mk _). destruct cell1. ss.
    Unshelve.
    { eapply Raw.remove_wf.
      - econs; eauto.
      - apply WF.
    }
  Qed.

  Lemma remove_get0
        cell1 from to msg cell2
        (REMOVE: remove cell1 from to msg cell2):
    <<GET: get to cell1 = Some (from, msg)>> /\
    <<GET: get to cell2 = None>>.
  Proof.
    inv REMOVE. splits; auto.
    unfold get. rewrite CELL2. rewrite DOMap.grspec. condtac; ss.
  Qed.


  (* maximal & minimal messages satisfying a property *)

  Lemma max_exists_aux P l:
    (<<NONE: forall ts (IN: List.In ts l), ~ P ts>>) \/
    exists max,
      (<<SAT: P max>>) /\
      (<<MAX: forall ts (IN: List.In ts l) (SAT: P ts),
          Time.le ts max>>).
  Proof.
    induction l; auto. des; subst.
    - destruct (classic (P a)).
      + right. esplits; eauto.
        i. inv IN; try refl.
        exploit NONE; eauto. ss.
      + left. ii. inv IN; ss.
        exploit NONE; eauto.
    - right. destruct (classic (P a)).
      + destruct (TimeFacts.le_lt_dec a max).
        * exists max. splits; ss.
          i. des; subst; eauto.
        * exists a. splits; ss.
          i. des; subst; try refl.
          exploit MAX; eauto. i.
          etrans; eauto. econs. ss.
      + esplits; eauto. i. inv IN; eauto. ss.
  Qed.

  Lemma max_exists P cell:
    (<<NONE: forall from to msg
                    (GET: get to cell = Some (from, msg)),
        ~ P to>>) \/
    exists from_max to_max msg_max,
      (<<GET: get to_max cell = Some (from_max, msg_max)>>) /\
      (<<SAT: P to_max>>) /\
      (<<MAX: forall from to msg
                     (GET: get to cell = Some (from, msg))
                     (SAT: P to),
          Time.le to to_max>>).
  Proof.
    specialize (finite cell). i. des.
    specialize (max_exists_aux
                  (fun ts => P ts /\
                             exists from msg,
                               get ts cell = Some (from, msg))
                  dom).
    i. des.
    - left. ii. exploit H; eauto. i.
      exploit NONE; eauto.
    - right. esplits; eauto. i.
      exploit H; eauto.
  Qed.

  Lemma min_exists_aux P l:
    (<<NONE: forall ts (IN: List.In ts l), ~ P ts>>) \/
    exists min,
      (<<SAT: P min>>) /\
      (<<MIN: forall ts (IN: List.In ts l) (SAT: P ts),
          Time.le min ts>>).
  Proof.
    induction l; auto. des; subst.
    - destruct (classic (P a)).
      + right. esplits; eauto.
        i. inv IN; try refl.
        exploit NONE; eauto. ss.
      + left. ii. inv IN; ss.
        exploit NONE; eauto.
    - right. destruct (classic (P a)).
      + destruct (TimeFacts.le_lt_dec min a).
        * exists min. splits; ss.
          i. des; subst; eauto.
        * exists a. splits; ss.
          i. des; subst; try refl.
          exploit MIN; eauto. i.
          etrans; eauto. econs. ss.
      + esplits; eauto. i. inv IN; eauto. ss.
  Qed.

  Lemma min_exists P cell:
    (<<NONE: forall from to msg
                    (GET: get to cell = Some (from, msg)),
        ~ P to>>) \/
    exists from_min to_min msg_min,
      (<<GET: get to_min cell = Some (from_min, msg_min)>>) /\
      (<<SAT: P to_min>>) /\
      (<<MIN: forall from to msg
                     (GET: get to cell = Some (from, msg))
                     (SAT: P to),
          Time.le to_min to>>).
  Proof.
    specialize (finite cell). i. des.
    specialize (min_exists_aux
                  (fun ts => P ts /\
                             exists from msg,
                               get ts cell = Some (from, msg))
                  dom).
    i. des.
    - left. ii. exploit H; eauto. i.
      exploit NONE; eauto.
    - right. esplits; eauto. i.
      exploit H; eauto.
  Qed.


  (* next & previous greater timestamp *)

  Lemma next_exists
        cell f t m ts
        (INHABITED: get t cell = Some (f, m))
        (TS: Time.lt ts (max_ts cell)):
    exists from to msg,
      get to cell = Some (from, msg) /\
      Time.lt ts to /\
      forall ts' (TS1: Time.lt ts ts') (TS2: Time.lt ts' to),
        get ts' cell = None.
  Proof.
    specialize (min_exists (fun ts' => Time.lt ts ts') cell). i. des.
    - exploit max_ts_spec; eauto. i. des.
      exploit NONE; eauto. ss.
    - esplits; try exact GET; eauto. i.
      destruct (get ts' cell) as [[]|] eqn:GET'; ss.
      exploit MIN; try exact GET'; ss. i. timetac.
  Qed.

  Lemma prev_exists
        cell f t m ts
        (INHABITED: get t cell = Some (f, m))
        (TS: Time.lt t ts):
    exists from to msg,
      get to cell = Some (from, msg) /\
      Time.lt to ts /\
      forall ts' (TS1: Time.lt to ts') (TS2: Time.lt ts' ts),
        get ts' cell = None.
  Proof.
    specialize (max_exists (fun ts' => Time.lt ts' ts) cell). i. des.
    - exploit NONE; eauto. ss.
    - esplits; try exact GET; eauto. i.
      destruct (get ts' cell) as [[]|] eqn:GET'; ss.
      exploit MAX; try exact GET'; ss. i. timetac.
  Qed.


  (* adjacent *)

  Variant adjacent (from1 to1 from2 to2: Time.t) (cell: t): Prop :=
  | adjacent_intro
      m1 m2
      (GET1: get to1 cell = Some (from1, m1))
      (GET2: get to2 cell = Some (from2, m2))
      (TS: Time.lt to1 to2)
      (EMPTY: forall ts (TS1: Time.lt to1 ts) (TS2: Time.le ts from2),
          get ts cell = None)
  .

  Lemma adjacent_ts
        from1 to1 from2 to2 mem
        (ADJ: adjacent from1 to1 from2 to2 mem):
    Time.le to1 from2.
  Proof.
    destruct (Time.le_lt_dec to1 from2); auto.
    exfalso. inv ADJ.
    exploit get_ts; try exact GET1. i.
    exploit get_ts; try exact GET2. i.
    exploit get_disjoint; [exact GET1|exact GET2|..]. i. des.
    { subst. timetac. }
    apply (x2 to1); econs; ss.
    - refl.
    - econs. auto.
  Qed.

  Lemma adjacent_inj
        to mem
        from1 from2 from3 to3 from4 to4
        (ADJ1: adjacent from1 to from3 to3 mem)
        (ADJ2: adjacent from2 to from4 to4 mem):
    from1 = from2 /\ from3 = from4 /\ to3 = to4.
  Proof.
    inv ADJ1. inv ADJ2.
    destruct (Time.le_lt_dec to3 to4); cycle 1.
    { exfalso.
      destruct (Time.le_lt_dec to4 from3).
      - exploit EMPTY; try exact l0; eauto. i. congruence.
      - exploit get_ts; try exact GET2. i.
        exploit get_ts; try exact GET3. i.
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x2 to4); econs; ss.
        + econs. ss.
        + refl. }
    inv l.
    { exfalso.
      destruct (Time.le_lt_dec to3 from4).
      - exploit EMPTY0; try exact l; eauto. i. congruence.
      - exploit get_ts; try exact GET2. i.
        exploit get_ts; try exact GET3. i.
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x2 to3); econs; ss.
        + refl.
        + econs. ss. }
    inv H. splits; auto.
  Qed.

  Lemma adjacent_exists
        from1 to1 msg cell
        (GET: get to1 cell = Some (from1, msg))
        (TO: Time.lt to1 (max_ts cell)):
    exists from2 to2,
      adjacent from1 to1 from2 to2 cell.
  Proof.
    exploit next_exists; eauto. i. des.
    esplits. econs; try exact x0; eauto. i.
    eapply x2; eauto.
    exploit get_ts; try exact x0. i.
    eapply TimeFacts.le_lt_lt; eauto.
  Qed.


  (* cap *)

  Variant cap (cell1 cell2: t): Prop :=
  | cap_intro
      (SOUND: le cell1 cell2)
      (MIDDLE: forall from1 to1 from2 to2
                 (ADJ: adjacent from1 to1 from2 to2 cell1)
                 (TO: Time.lt to1 from2),
          get from2 cell2 = Some (to1, Message.reserve))
      (BACK: forall from msg
               (GET: get (max_ts cell1) cell1 = Some (from, msg)),
          get (Time.incr (max_ts cell1)) cell2 =
          Some (max_ts cell1, Message.reserve))
      (COMPLETE: forall from to msg
                   (GET1: get to cell1 = None)
                   (GET2: get to cell2 = Some (from, msg)),
          (exists f m, get from cell1 = Some (f, m)))
  .

  Variant cap_aux (dom: list Time.t) (cell1 cell2: t): Prop :=
  | cap_aux_intro
      (SOUND: le cell1 cell2)
      (MIDDLE: forall from1 to1 from2 to2
                 (IN: List.In to1 dom)
                 (ADJ: adjacent from1 to1 from2 to2 cell1)
                 (TO: Time.lt to1 from2),
          get from2 cell2 = Some (to1, Message.reserve))
      (BACK: forall from msg
               (IN: List.In (max_ts cell1) dom)
               (GET: get (max_ts cell1) cell1 = Some (from, msg)),
          get (Time.incr (max_ts cell1)) cell2 =
          Some (max_ts cell1, Message.reserve))
      (COMPLETE: forall from to msg
                   (GET1: get to cell1 = None)
                   (GET2: get to cell2 = Some (from, msg)),
          List.In from dom /\
          (exists f m, get from cell1 = Some (f, m)))
  .

  Lemma cap_aux_exists dom cell1:
    exists cell2, cap_aux dom cell1 cell2.
  Proof.
    revert cell1.
    induction dom; i.
    { exists cell1. econs; ss; i. congruence. }
    exploit IHdom; eauto. intros x. des. clear IHdom.
    destruct (ListDec.In_decidable time_decidable a dom).
    { exists cell2. inv x. econs; ii; eauto.
      - inv IN; eauto.
      - inv IN; eauto.
      - exploit COMPLETE; eauto. i. des.
        split; eauto. econs 2; eauto.
    }
    destruct (get a cell1) as [[from msg]|] eqn:GET1; cycle 1.
    { exists cell2. inv x. econs; ii; eauto.
      - inv IN; eauto. inv ADJ.
      - inv IN; eauto.
      - exploit COMPLETE; eauto. i. des.
        split; eauto. econs 2; eauto.
    }
    exploit max_ts_spec; eauto. i. des.
    inv MAX.
    { exploit adjacent_exists; try exact GET1; ss. i. des.
      exploit adjacent_ts; eauto. i. inv x2; cycle 1.
      { inv H1.
        exists cell2. inv x. econs; ii; eauto.
        - inv IN; eauto.
          exploit adjacent_inj; [exact x1|exact ADJ|..]. i. des. subst.
          timetac.
        - inv IN; eauto. timetac.
        - exploit COMPLETE; eauto. i. des.
          split; eauto. econs 2; eauto.
      }
      exploit (@add_exists cell2 a from2 Message.reserve); ii.
      { inv x. inv x1. inv LHS. inv RHS. ss.
        clear MIDDLE BACK.
        destruct (get to0 cell1) as [[]|] eqn:GET4.
        - exploit SOUND; try exact GET4. intros x.
          rewrite x in GET2. inv GET2.
          destruct (Time.le_lt_dec to0 from2).
          { exploit (EMPTY to0); try congruence.
            eapply TimeFacts.lt_le_lt; try exact FROM; ss. }
          exploit get_ts; try exact GET3. i.
          exploit get_ts; try exact GET4. i.
          exploit get_disjoint; [exact GET3|exact GET4|..]. i. des.
          { subst. timetac. }
          destruct (Time.le_lt_dec to0 to2).
          + apply (x4 to0); econs; ss; try refl.
          + apply (x4 to2); econs; ss; try refl.
            * eapply TimeFacts.le_lt_lt; try exact x2.
              etrans; try exact TO. econs. ss.
            * econs. ss.
        - exploit COMPLETE; try exact GET2; eauto. intros x. des.
          cut (from1 = a); try by (i; subst; ss).
          clear COMPLETE.
          destruct (Time.le_lt_dec from1 a).
          + inv l; try by (inv H2; ss).
            exploit SOUND; try exact GET1. intros x2.
            exploit get_ts; try exact x2. i.
            exploit get_disjoint; [exact x2|exact GET2|..]. i. des.
            { subst. timetac. }
            exfalso.
            apply (x5 a); econs; ss; try refl.
            econs. eapply TimeFacts.lt_le_lt; try exact FROM. ss.
          + exploit (EMPTY from1); try congruence.
            econs. eapply TimeFacts.lt_le_lt; try exact FROM0. ss.
      }
      { ss. }
      des.
      exists cell0. inv x. econs; ii; ss.
      - exploit SOUND; eauto. i.
        eapply add_get1; eauto.
      - exploit add_get0; eauto. i. des.
        des; subst.
        + exploit adjacent_inj; [exact x1|exact ADJ|..]. i. des.
          subst. ss.
        + exploit MIDDLE; eauto. i.
          eapply add_get1; eauto.
      - des; subst; timetac.
        exploit BACK; eauto. i.
        eapply add_get1; eauto.
      - revert GET2. erewrite add_o; eauto. condtac; ss; i.
        + subst. inv GET2. splits; eauto.
        + exploit COMPLETE; eauto. i. des.
          esplits; eauto.
    }
    inv H0. 
    exploit (@add_exists cell2 (max_ts cell1) (Time.incr (max_ts cell1)) Message.reserve); ii.
    { inv x. inv LHS. inv RHS. ss.
      destruct (get to2 cell1) as [[]|] eqn:GET3.
      { exploit SOUND; eauto. intros x.
        rewrite x in GET2. inv GET2.
        exploit max_ts_spec; try exact GET3. i. des.
        exploit TimeFacts.le_lt_lt; try exact FROM; try exact MAX. i.
        timetac. }
      exploit COMPLETE; eauto. intros x. des.
      cut (from2 = max_ts cell1); try by (i; subst; ss).
      destruct (Time.le_lt_dec from2 (max_ts cell1)).
      - inv l; try by (inv H0; ss).
        exploit SOUND; try exact GET1. intros x2.
        exploit get_ts; try exact x2. i.
        exploit get_ts; try exact GET2. i.
        exploit get_disjoint; [exact x2|exact GET2|..]. i. des.
        { subst. timetac. }
        exfalso.
        apply (x6 (max_ts cell1)); econs; ss; try refl.
        econs. eapply TimeFacts.lt_le_lt; try exact FROM. ss.
      - exploit max_ts_spec; try exact x1. i. des.
        timetac.
    }
    { apply Time.incr_spec. }
    des.
    exists cell0. inv x. econs; ii; ss; eauto.
    - exploit SOUND; eauto. i.
      eapply add_get1; eauto.
    - exploit add_get0; eauto. i. des.
      + inv ADJ. exploit max_ts_spec; try exact GET3. i. des. timetac.
      + eapply add_get1; eauto.
    - eapply add_get0; eauto.
    - revert GET2. erewrite add_o; eauto. condtac; ss; i.
      + subst. inv GET2. esplits; eauto.
      + exploit COMPLETE; eauto. i. des.
        esplits; eauto.
  Qed.

  Lemma cap_exists cell1:
    exists cell2, cap cell1 cell2.
  Proof.
    destruct (@finite cell1).
    exploit (@cap_aux_exists x); eauto. i. des.
    exists cell2. inv x1. econs; i; ss; eauto.
    - eapply MIDDLE; eauto. inv ADJ. eauto.
    - exploit COMPLETE; eauto. i. des.
      esplits; eauto.
  Qed.

  (* Additional *)
  Program Definition cut (C : Cell.t) (t : Time.t) : Cell.t :=
    @Cell.mk (DOMap.cut (Cell.raw C) t) _.
  Next Obligation.
    intros C t; econs.
    { intros from to msg FIND%DOMap.cut_find; hexploit (C.(Cell.WF)); intros [I _]; eauto. }
    { intros to1 to2 from1 from2 msg1 msg2 FIND1%DOMap.cut_find FIND2%DOMap.cut_find NEQ.
      hexploit (C.(Cell.WF)); intros [_ D]; eauto.
    }
  Defined.

  Lemma cut_spec (C : Cell.t) (t t_cut : Time.t) :
    Cell.get t (cut C t_cut) =
    if (Time.le_lt_dec t_cut t) then Cell.get t C else None.
  Proof. rewrite /cut /Cell.get /= DOMap.cut_spec; des_ifs; ss. Qed.

  Lemma cut_join (C : Cell.t) (t1 t2 : Time.t)
    (LE : Time.le t1 t2) :
    cut C t2 = cut (cut C t1) t2.
  Proof. 
    apply Cell.ext. intros ts.
    rewrite /Cell.get /cut /=; repeat (rewrite DOMap.cut_spec); des_ifs.
    exfalso. eapply TimeFacts.le_not_lt; eauto.
    eapply TimeFacts.lt_le_lt; eauto.
  Qed.

  Lemma cut_singleton_lt_get cell from to msg t_cut ts
        (FT: Time.lt from to)
        (CUT: Time.le t_cut to)
        (LT : Time.lt to ts)
        (SINGLETON: cut cell t_cut = Cell.singleton msg FT) :
    Cell.get ts cell = None.
  Proof.
    destruct (get ts cell) eqn:GET; eauto.
    apply (f_equal (get ts)) in SINGLETON.
    rewrite Cell.cut_spec Cell.singleton_get in SINGLETON.
    des_ifs; timetac.
    exfalso. eapply TimeFacts.le_not_lt. eapply CUT. trans ts; timetac.
  Qed.

  Lemma cut_singleton_add cell1 from1 to1 msg1 cell2 from2 to2 msg2 Vcut
        (FT1: Time.lt from1 to1)
        (FT2: Time.lt from2 to2)
        (CUT: Time.le Vcut to1)
        (LT : Time.lt to1 to2)
        (SINGLETON: cut cell1 Vcut = Cell.singleton msg1 FT1)
        (ADD: add cell1 from2 to2 msg2 cell2) :
      cut cell2 to2 = @Cell.singleton from2 to2 msg2 FT2.
  Proof.
    apply Cell.ext. intros ts. inv ADD.
    rewrite Cell.cut_spec. 
    rewrite /Cell.get /cut /=; repeat (rewrite DOMap.cut_spec).
    destruct (decide (to2 = ts)); subst.
    { des_ifs.
      { rewrite CELL2. repeat (rewrite DOMap.gss //). }
      { timetac. }
    }
    { des_ifs. inv l; timetac.
      { rewrite CELL2. repeat (rewrite DOMap.gso //).
        hexploit cut_singleton_lt_get; 
          [eapply CUT | etrans; eauto | apply SINGLETON | idtac]; intro GET.
        rewrite /get in GET. rewrite GET.
        rewrite ?DOMap.gempty; ss.
      }
      { repeat (rewrite DOMap.gso //). 
        rewrite ?DOMap.gempty; ss.
      }
    }
  Qed.

  Definition to_gmap (C : t) : gmap Time.t (Time.t * Message.t) :=
    list_to_map (DOMap.elements (Cell.raw C)).
    (* DOMap.fold (λ k a m, <[ k := a ]> m ) (Cell.raw C) ∅. *)
  
  Lemma to_gmap_spec (C : t) : ∀ ts, Cell.get ts C = to_gmap C !! ts.
  Proof.
    rewrite /get /to_gmap.
    intros ts; destruct (DOMap.find ts (Cell.raw C)) eqn : FINDC.
    { erewrite elem_of_list_to_map_1'; eauto.
      { intros y IN%elem_of_list_In%DOMap.elements_complete; clarify. }
      { apply elem_of_list_In, DOMap.elements_correct; ss. }
    }
    { rewrite not_elem_of_list_to_map_1; ss.
      intros [[ts' msg] [EQ IN]]%elem_of_list_In%in_map_iff.
      ss; subst; hexploit DOMap.elements_complete; eauto; ii; clarify.
    }
  Qed.
End Cell.