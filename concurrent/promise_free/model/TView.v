Require Import CRIS.common.CRIS.

From CRIS.promise_free.lib Require Import
  Basic DataStructure Loc Language Event Ordering.

From CRIS.promise_free.model Require Import Time View Cell Memory.

Set Implicit Arguments.


Module TView <: JoinableType.
  Structure t_ := mk {
    rel: LocFun.t View.t;
    cur: View.t;
    acq: View.t;
  }.
  Definition t := t_.

  (* Definition bot: t := mk (LocFun.init View.bot) View.bot View.bot. *)

  Definition init size: t := mk (LocFun.init (View.init size)) (View.init size) (View.init size).

  Variant wf (tview:t): Prop :=
  | wf_intro
      (* (REL: forall loc, View.wf ((rel tview) loc)) *)
      (* (CUR: View.wf (cur tview)) *)
      (* (ACQ: View.wf (acq tview)) *)
      (REL_CUR: forall loc, View.le ((rel tview) loc) (cur tview))
      (CUR_ACQ: View.le (cur tview) (acq tview))
  .

  Variant closed (tview:t) (mem:Memory.t): Prop :=
  | closed_intro
      (REL: forall loc, Memory.closed_view ((rel tview) loc) mem)
      (CUR: Memory.closed_view (cur tview) mem)
      (ACQ: Memory.closed_view (acq tview) mem)
  .

  (* Lemma bot_wf: wf bot. *)
  (* Proof. *)
  (*   econs; i; econs; refl. *)
  (* Qed. *)

  (* Lemma bot_closed: closed bot Memory.bot. *)
  (* Proof. *)
  (*   econs; i; eapply Memory.closed_view_bot. *)
  (* Qed. *)

  Lemma init_wf size: wf (init size).
  Proof.
    econs; i; ss; refl.
  Qed.

  Lemma init_closed l: closed (init l) (Memory.init l).
  Proof.
    econs; i; ss; eapply Memory.closed_view_init.
  Qed.

  Lemma le_closed
        tview mem1 mem2
        (CLOSED: closed tview mem1)
        (LE: Memory.messages_le mem1 mem2):
    closed tview mem2.
  Proof.
    inv CLOSED. econs; i; eapply Memory.messages_le_closed_view; eauto.
  Qed.

  Lemma future_closed
        tview mem1 mem2
        (CLOSED: closed tview mem1)
        (FUTURE: Memory.future mem1 mem2):
    closed tview mem2.
  Proof.
    inv CLOSED. econs; i; eapply Memory.future_closed_view; eauto.
  Qed.

  Lemma cap_closed
    tview mem cap
    (CLOSED: closed tview mem)
    (CAP: Memory.cap mem cap):
    closed tview cap.
  Proof.
    inv CLOSED. econs; eauto using Memory.cap_closed_view.
  Qed.

  Definition eq := @eq t.

  Variant le_ (lhs rhs:t): Prop :=
  | le_intro
      (REL: forall (loc:Loc.t), View.le (LocFun.find loc (rel lhs)) (LocFun.find loc (rel rhs)))
      (CUR: View.le (cur lhs) (cur rhs))
      (ACQ: View.le (acq lhs) (acq rhs))
  .
  Definition le := le_.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Definition join (lhs rhs:t): t :=
    mk (fun loc => View.join ((rel lhs) loc) ((rel rhs) loc))
       (View.join (cur lhs) (cur rhs))
       (View.join (acq lhs) (acq rhs)).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    unfold join. f_equal.
    - apply LocFun.ext. i. apply View.join_comm.
    - apply View.join_comm.
    - apply View.join_comm.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join. s. f_equal.
    - apply LocFun.ext. i. apply View.join_assoc.
    - apply View.join_assoc.
    - apply View.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof.
    econs.
    - i. apply View.join_l.
    - apply View.join_l.
    - apply View.join_l.
  Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof.
    econs.
    - i. apply View.join_r.
    - apply View.join_r.
    - apply View.join_r.
  Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    inv LHS. inv RHS. econs.
    - i. apply View.join_spec; eauto.
    - apply View.join_spec; eauto.
    - apply View.join_spec; eauto.
  Qed.

  Lemma join_closed
        lhs rhs mem
        (LHS: closed lhs mem)
        (RHS: closed rhs mem):
    closed (join lhs rhs) mem.
  Proof.
    inv LHS. inv RHS. econs; i; try eapply Memory.join_closed_view; eauto.
  Qed.
   
  Definition racy_view (view: View.t) (loc: Loc.t) (ts: Time.t): Prop :=
    Time.lt ((View.rlx view) loc) ts.

  Variant readable (view1:View.t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): Prop :=
  | readable_intro
      (RLX: Time.le ((View.rlx view1) loc) ts)
      (ALLOCED: (View.alloc_view view1) (Loc.get_tbid loc))
  .

  Definition read_tview (tview1:t) (loc:Loc.t) (ts:Time.t) (released:View.t) (ord:Ordering.t): t :=
    mk (rel tview1)
       (View.join
          (View.join
             (cur tview1)
             (View.singleton loc ts))
          (if Ordering.le Ordering.acqrel ord then released else View.bot))
       (View.join
          (View.join
             (acq tview1)
             (View.singleton loc ts))
          (if Ordering.le Ordering.relaxed ord then released else View.bot)).

  Variant writable (view1:View.t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): Prop :=
  | writable_intro
      (TS: Time.lt ((View.rlx view1) loc) ts)
      (ALLOCED: (View.alloc_view view1) (Loc.get_tbid loc))
  .

  Definition write_tview (tview1:t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): t :=
    let cur2 := View.join
                  (cur tview1)
                  (View.singleton loc ts)
    in
    let acq2 := View.join
                  (acq tview1)
                  (View.singleton loc ts)
    in
    let rel2 := LocFun.add loc
                     (if Ordering.le Ordering.acqrel ord then cur2 else View.join ((rel tview1) loc) (View.singleton loc ts))
                  (rel tview1)
    in
    mk rel2 cur2 acq2.

  Definition write_released tview loc ts releasedm ord :=
    if Ordering.le Ordering.relaxed ord
    then View.join
           releasedm
           ((rel (write_tview tview loc ts ord)) loc)
    else View.bot.

  Definition alloc_tview (tview1:t) (loc:Loc.t) (size:Z): t :=
    let cur2 := View.join (cur tview1) (View.alloc_view_singleton loc size) in
    let acq2 := View.join (acq tview1) (View.alloc_view_singleton loc size) in
    mk (rel tview1) cur2 acq2.

  Definition read_fence_tview
             (tview1:t) (ord:Ordering.t): t :=
    mk (rel tview1)
                (if Ordering.le Ordering.acqrel ord
                 then (acq tview1)
                 else (cur tview1))
                (acq tview1).

  Definition write_fence_sc
             (tview1:t) (sc1:View.t) (ord:Ordering.t): View.t :=
    if Ordering.le Ordering.seqcst ord
    then View.join sc1 (cur tview1)
    else sc1.

  Definition write_fence_tview
             (tview1:t) (sc1:View.t) (ord:Ordering.t): t :=
    let sc2 := write_fence_sc tview1 sc1 ord in
    let cur2 := if Ordering.le Ordering.seqcst ord then sc2 else (cur tview1) in
    let acq2 := View.join
                  (acq tview1)
		  (if Ordering.le Ordering.seqcst ord then sc2 else View.bot)
    in
    let rel2 := fun l => if Ordering.le Ordering.acqrel ord then cur2 else ((rel tview1) l) in
    mk rel2 cur2 acq2.

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    destruct l, r. inv LR. inv RL. ss. f_equal.
    - apply LocFun.ext. i. apply View.antisym; auto.
    - apply View.antisym; auto.
    - apply View.antisym; auto.
  Qed.
End TView.


Module TViewFacts.
  Ltac tac :=
    repeat
      (try match goal with
           | [H: ?a <> ?a |- _] => congruence
           | [H: Memory.closed ?mem |- Memory.inhabited ?mem] =>
             apply H
           | [|- View.le ?s ?s] =>
             refl
           | [|- TimeMap.le ?s ?s] =>
             refl
           | [|- View.le View.bot ?s] =>
             apply View.bot_spec
           | [|- TimeMap.le TimeMap.bot _] =>
             apply TimeMap.bot_spec
           | [|- Time.le (TimeMap.bot _) _] =>
             apply Time.bot_spec
           | [|- Time.le (LocFun.init Time.bot _) _] =>
             apply Time.bot_spec
           | [|- View.le ?s (View.join _ ?s)] =>
             apply View.join_r
           | [|- View.le ?s (View.join ?s _)] =>
             apply View.join_l
           | [|- TimeMap.le ?s (TimeMap.join _ ?s)] =>
             apply TimeMap.join_r
           | [|- TimeMap.le ?s (TimeMap.join ?s _)] =>
             apply TimeMap.join_l
           | [|- Memory.closed_view View.bot ?m] =>
             apply Memory.closed_view_bot
           | [WF: TView.wf ?c |- View.le ((TView.rel ?c) ?l) (TView.cur ?c)] =>
             apply WF
           | [WF: TView.wf ?c |- View.le ((TView.rel ?c) ?l) (TView.acq ?c)] =>
             etrans; apply WF
           | [WF: TView.wf ?c |- View.le (TView.cur ?c) (TView.acq ?c)] =>
             apply WF

           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: Ordering.le Ordering.acqrel ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: Ordering.le Ordering.seqcst ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.acqrel),
              H2: Ordering.le Ordering.seqcst ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.na),
              H2: Ordering.le Ordering.acqrel ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.na),
              H2: Ordering.le Ordering.relaxed ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.na),
              H2: is_true (Ordering.le Ordering.relaxed ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.na),
              H2: is_true (Ordering.le Ordering.seqcst ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.acqrel),
              H2: is_true (Ordering.le Ordering.seqcst ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: is_true (Ordering.le Ordering.seqcst ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o1 ?o2),
              H2: Ordering.le ?o0 ?o1 = true,
              H3: Ordering.le ?o0 ?o2 = false |- _] =>
               by destruct o1, o2; inv H1; inv H2; inv H3

           | [|- View.le (View.join _ _) _] =>
             apply View.join_spec
           | [|- TimeMap.le (TimeMap.singleton _ _) _] =>
             apply TimeMap.singleton_spec
           | [|- TimeMap.le (TimeMap.join _ _) _] =>
             apply TimeMap.join_spec
           | [|- Time.le (TimeMap.join _ _ _) _] =>
             apply Time.join_spec
           | [|- Time.lt (TimeMap.join _ _ _) _] =>
             apply TimeFacts.join_spec_lt

           | [|- Memory.closed_view (View.join _ _) _] =>
             eapply Memory.join_closed_view; eauto
           | [|- Memory.closed_view (View.singleton _ _) _] =>
             eapply Memory.singleton_closed_view; eauto
           (* | [|- Memory.closed_view View.init _] => *)
           (*   eapply Memory.init_closed_view; eauto *)

           | [H1: Memory.closed_view ?c ?m1,
              H2: Memory.future ?tid ?m1 ?m2 |-
              Memory.closed_view ?c ?m2] =>
             eapply Memory.future_closed_view; [exact H2|exact H1]

           | [H: Time.lt ?a ?b |- Time.le ?a ?b] =>
             left; apply H
           | [|- Time.le ?a ?a] =>
             refl
           (* | [|- View.le (View.mk ?tm1 ?tm1) (View.mk ?tm2 ?tm2)] => *)
           (*   apply View.timemap_le_le *)
           | [|- context[LocFun.find _ (LocFun.add _ _ _)]] =>
             rewrite LocFun.add_spec
           | [|- context[TimeMap.singleton ?l _ ?l]] =>
             unfold TimeMap.singleton
           | [|- context[LocFun.add ?l _ _ ?l]] =>
             unfold LocFun.add;
             match goal with
             | [|- context[Loc.eq_dec ?l ?l]] =>
               destruct (Loc.eq_dec l l); [|congruence]
             end
           | [|- context[LocFun.find _ _]] =>
             unfold LocFun.find
           | [|- context[LocFun.add _ _ _]] =>
             unfold LocFun.add

           | [H: _ <> _ |- _] => inv H
           end; subst; ss; i).

  Ltac aggrtac :=
    repeat
      (tac;
       try match goal with
           | [|- Time.le ?t1 (TimeMap.singleton ?l ?t2 ?l)] =>
             unfold TimeMap.singleton, LocFun.add; condtac; [|congruence]
           | [|- View.le _ (View.join _ _)] =>
             try (by rewrite <- View.join_l; aggrtac);
             try (by rewrite <- View.join_r; aggrtac)
           | [|- TimeMap.le _ (TimeMap.join _ _)] =>
             try (by rewrite <- TimeMap.join_l; aggrtac);
             try (by rewrite <- TimeMap.join_r; aggrtac)
           | [|- Time.le _ (TimeMap.join _ _ _)] =>
             try (by etrans; [|by apply Time.join_l]; aggrtac);
             try (by etrans; [|by apply Time.join_r]; aggrtac)

           (* | [|- View.le _ (View.mk ?tm ?tm)] => *)
           (*   apply rlx_le_view_le *)
           end).

  Lemma read_tview_incr
        tview1 loc ts released ord:
    TView.le tview1 (TView.read_tview tview1 loc ts released ord).
  Proof.
    econs; tac.
    - rewrite <- ? View.join_l. refl.
    - rewrite <- ? View.join_l. refl.
  Qed.

  Lemma write_tview_incr
        tview1 loc ts ord
        (WF1: TView.wf tview1):
    TView.le tview1 (TView.write_tview tview1 loc ts ord).
  Proof.
    econs; repeat (try condtac; aggrtac).
  Qed.

  Lemma read_fence_tview_incr
        tview1 ord
        (WF1: TView.wf tview1):
    TView.le tview1 (TView.read_fence_tview tview1 ord).
  Proof.
    econs; tac. condtac; tac.
  Qed.

  Lemma write_fence_tview_incr
        tview1 sc1 ord
        (WF1: TView.wf tview1):
    TView.le tview1 (TView.write_fence_tview tview1 sc1 ord).
  Proof.
    unfold TView.write_fence_tview, TView.write_fence_sc.
    econs; repeat (try condtac; aggrtac; try apply WF1).
  Qed.

  Lemma write_fence_sc_incr
        tview1 sc1 ord:
    View.le sc1 (TView.write_fence_sc tview1 sc1 ord).
  Proof.
    unfold TView.write_fence_sc. condtac; tac.
  Qed.

  Lemma racy_view_mon
        view1 view2 loc ts
        (VIEW: View.le view1 view2)
        (RACE: TView.racy_view view2 loc ts):
    TView.racy_view view1 loc ts.
  Proof.
    unfold TView.racy_view in *. inv VIEW. specialize (RLX loc).
    eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma readable_mon
        view1 view2 loc ts ord1 ord2
        (VIEW: View.le view1 view2)
        (ORD: Ordering.le ord1 ord2)
        (READABLE: TView.readable view2 loc ts ord2)
        (ALLOCED: (View.alloc_view view1) (Loc.get_tbid loc)):
    TView.readable view1 loc ts ord1.
  Proof.
    inv READABLE. inv VIEW. econs; eauto.
    etrans; eauto.
  Qed.

  Lemma writable_mon
        view1 view2 loc ts ord1 ord2
        (VIEW: View.le view1 view2)
        (ORD: Ordering.le ord1 ord2)
        (WRITABLE: TView.writable view2 loc ts ord2)
        (ALLOCED: (View.alloc_view view1) (Loc.get_tbid loc)):
    TView.writable view1 loc ts ord1.
  Proof.
    inv WRITABLE. inv VIEW. econs; eauto.
    specialize (RLX loc). eapply TimeFacts.le_lt_lt; try apply RLX; auto.
  Qed.

  Lemma read_tview_mon
        tview1 tview2 loc ts released1 released2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (REL: View.le released1 released2)
        (WF2: TView.wf tview2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.read_tview tview1 loc ts released1 ord1)
      (TView.read_tview tview2 loc ts released2 ord2).
  Proof.
    unfold TView.read_tview, View.singleton.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2);
      (try by etrans; [|apply View.join_l]; etrans; [|apply View.join_l]; apply WF2).
  Qed.

  Lemma write_tview_mon
        tview1 tview2 loc ts ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (WF2: TView.wf tview2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.write_tview tview1 loc ts ord1)
      (TView.write_tview tview2 loc ts ord2).
  Proof.
    unfold TView.write_tview, View.singleton.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
  Qed.

  Lemma write_released_mon
        tview1 tview2 loc ts releasedm1 releasedm2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (WF2: TView.wf tview2)
        (RELM_LE: View.le releasedm1 releasedm2)
        (ORD: Ordering.le ord1 ord2):
    View.le
      (TView.write_released tview1 loc ts releasedm1 ord1)
      (TView.write_released tview2 loc ts releasedm2 ord2).
  Proof.
    unfold TView.write_released, TView.write_tview.
    destruct (Ordering.le Ordering.relaxed ord1) eqn:ORD1,
             (Ordering.le Ordering.relaxed ord2) eqn:ORD2; tac;
      repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try by rewrite <- ? TimeMap.join_l; apply RELM);
      (try by rewrite <- TimeMap.join_r, <- ? TimeMap.join_l; etrans; [apply TVIEW|apply WF2]);
      (try apply WF2);
      (try by etrans; [|apply View.join_r]; etrans; [|apply View.join_l]; apply WF2).
  Qed.

  Lemma read_fence_tview_mon
        tview1 tview2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (WF2: TView.wf tview2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.read_fence_tview tview1 ord1)
      (TView.read_fence_tview tview2 ord2).
  Proof.
    unfold TView.read_fence_tview.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; aggrtac;
       rewrite <- ? TimeMap.join_r; apply TVIEW).
  Qed.

  Lemma write_fence_tview_mon
        tview1 tview2 sc1 sc2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (SC: View.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2)
        (WF1: TView.wf tview1):
    TView.le
      (TView.write_fence_tview tview1 sc1 ord1)
      (TView.write_fence_tview tview2 sc2 ord2).
  Proof.
    unfold TView.write_fence_tview, TView.write_fence_sc.
    econs; repeat (condtac; aggrtac).
    all: try by etrans; [apply TVIEW|aggrtac].
    all: try by apply WF1.
    all: try by rewrite <- ? View.join_r; aggrtac;
      (rewrite <- ? TimeMap.join_r; apply TVIEW);
      (try by apply WF1).
    - rewrite <- View.join_r. etrans; [apply WF1|]. apply TVIEW.
    - etrans; [apply WF1|]. apply TVIEW.
  Qed.

  Lemma write_fence_sc_mon
        tview1 tview2 sc1 sc2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (SC: View.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2):
    View.le
      (TView.write_fence_sc tview1 sc1 ord1)
      (TView.write_fence_sc tview2 sc2 ord2).
  Proof.
    unfold TView.write_fence_sc.
    repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try rewrite <- ? View.join_r; aggrtac;
       rewrite <- ? TimeMap.join_r; apply TVIEW).
  Qed.

  Lemma alloc_view_mon
        tview1 tview2 loc size
        (TVIEW: TView.le tview1 tview2):
    TView.le
      (TView.alloc_tview tview1 loc size)
      (TView.alloc_tview tview2 loc size).
  Proof.
    unfold TView.alloc_tview.
    econs; aggrtac; (try by etrans; [apply TVIEW| aggrtac]).
  Qed.

  Lemma write_fence_sc_acqrel
        tview sc ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    TView.write_fence_sc tview sc ordw = sc.
  Proof.
    unfold TView.write_fence_sc. condtac; tac.
  Qed.

  Lemma write_fence_tview_acqrel
        tview sc1 sc2 ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    TView.write_fence_tview tview sc1 ordw = TView.write_fence_tview tview sc2 ordw.
  Proof.
    unfold TView.write_fence_tview.
    apply TView.antisym; repeat (condtac; tac; try refl).
  Qed.

  Lemma write_fence_tview_strong_relaxed
        tview sc o (ORD: Ordering.le o Ordering.strong_relaxed):
    TView.write_fence_tview tview sc o = tview.
  Proof.
    unfold TView.write_fence_tview, TView.write_fence_sc.
    destruct tview. ss.
    f_equal; repeat (condtac; aggrtac); try by destruct o.
    rewrite View.join_comm View.join_bot_l. ss.
  Qed.

  Lemma read_future1
        loc from to val released na ord tview mem
        (WF_TVIEW: TView.wf tview)
        (GET: Memory.get loc to mem = Some (from, Message.message val released na)):
    <<WF_TVIEW: TView.wf (TView.read_tview tview loc to released ord)>>.
  Proof.
    econs; repeat (try condtac; tac);
      (try by rewrite <- ? View.join_l; apply WF_TVIEW);
      (try by econs; etrans; [|apply View.join_l]; etrans; [|apply View.join_l]; apply WF_TVIEW).
    - rewrite <- View.join_l. rewrite <- View.join_r. refl.
    - rewrite <- View.join_l. rewrite <- View.join_r. refl.
    - destruct ord; inv COND; inv COND0.
  Qed.

  Lemma read_future
        loc from to val released na ord tview mem
        (MEM: Memory.closed mem)
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem)
        (GET: Memory.get loc to mem = Some (from, Message.message val released na))
        (ALLOCED: ~ Memory.is_prealloced loc mem):
    <<WF_TVIEW: TView.wf (TView.read_tview tview loc to released ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.read_tview tview loc to released ord) mem>>.
  Proof.
    splits; try eapply read_future1; eauto.
    inv MEM. exploit CLOSED; eauto. i. des. inv MSG_CLOSED.
    econs; tac; try eapply CLOSED_TVIEW;
      try (by eapply Memory.singleton_closed_view; eauto);
      condtac; tac.
  Qed.

  Lemma write_closed_tview
        mem1 tview1 loc from to val released na ord mem2
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (WRITE: Memory.add mem1 loc from to (Message.message val released na) mem2)
        (ALLOCED: ~ Memory.is_prealloced loc mem1):
    TView.closed (TView.write_tview tview1 loc to ord) mem2.
  Proof.
    assert(ALLOCED2: ~ Memory.is_prealloced loc mem2).
    { exploit Memory.add_preserve; eauto. i. des.
      unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *.
      rewrite GET_STATE. eauto.
    }
    unfold TView.write_tview.
    econs; repeat (try condtac; tac);
      (try by eapply Memory.add_closed_view; eauto; apply CLOSED2);
      (try by econs; tac; eapply Memory.add_closed_view; eauto; apply CLOSED0);
      (try by eapply Memory.singleton_closed_view; eapply Memory.add_get0; eauto);
      (try by eapply Memory.add_get0; eauto).
  Qed.

  Lemma write_closed_released
        mem1 tview1 loc from to val releasedm released na ord mem2
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (CLOSED3: Memory.closed_view releasedm mem1)
        (WRITE: Memory.add mem1 loc from to (Message.message val released na) mem2)
        (ALLOCED: ~ Memory.is_prealloced loc mem1):
    Memory.closed_view (TView.write_released tview1 loc to releasedm ord) mem2.
  Proof.
    unfold TView.write_released. condtac; try by (econs; ss; try eapply Memory.closed_view_bot).
    apply Memory.join_closed_view.
    - eapply Memory.add_closed_view; eauto.
    - eapply write_closed_tview; eauto.
  Qed.

  Lemma get_closed_tview
        mem1 tview1 loc from to val released na ord
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (GET: Memory.get loc to mem1 = Some (from, Message.message val released na))
        (ALLOCED: ~ Memory.is_prealloced loc mem1):
    TView.closed (TView.write_tview tview1 loc to ord) mem1.
  Proof.
    econs; tac; repeat condtac; tac;
      (try by apply CLOSED2);
      (try by eapply Memory.singleton_closed_view; eauto).
  Qed.

  Lemma get_closed_released
        mem1 tview1 loc from to val releasedm released na ord
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (CLOSED3: Memory.closed_view releasedm mem1)
        (GET: Memory.get loc to mem1 = Some (from, Message.message val released na))
        (ALLOCED: ~ Memory.is_prealloced loc mem1):
    Memory.closed_view (TView.write_released tview1 loc to releasedm ord) mem1.
  Proof.
    unfold TView.write_released. condtac; try by (econs; ss; eapply Memory.closed_view_bot).
    - apply Memory.join_closed_view; ss.
      eapply get_closed_tview; eauto.
  Qed.

  Lemma write_released_ts
        loc to releasedm ord tview
        (WF_TVIEW: TView.wf tview)
        (WRITABLE: TView.writable (TView.cur tview) loc to ord)
        (RELEASEDM: Time.le ((View.rlx releasedm) loc) to):
    Time.le
      (View.rlx (TView.write_released tview loc to releasedm ord) loc)
      to.
  Proof.
    unfold TView.write_released.
    condtac; try apply Time.bot_spec. ss.
    apply Time.join_spec; ss.
    unfold LocFun.add. repeat condtac; ss.
    - apply Time.join_spec.
      + econs. apply WRITABLE.
      + unfold TimeMap.singleton, LocFun.add. condtac; ss. refl.
    - apply Time.join_spec.
      + etrans; try apply WF_TVIEW. econs. apply WRITABLE.
      + unfold TimeMap.singleton, LocFun.add. condtac; ss. refl.
    (* - inv WRITABLE. econs. eapply TimeFacts.le_lt_lt; [|apply TS]. apply WF_TVIEW. *)
  Qed.

  Lemma write_future0
        loc to ord tview
        (WF_TVIEW: TView.wf tview):
    <<WF_TVIEW: TView.wf (TView.write_tview tview loc to ord)>>.
  Proof.
    splits; tac. econs; tac; try apply WF_TVIEW; repeat (try condtac; tac);
      (try by econs; etrans;[|apply View.join_l]; apply WF_TVIEW);
      (try by econs; apply WF_TVIEW);
      (try by aggrtac; rewrite <- ? View.join_l; try apply WF_TVIEW).
  Qed.

  Lemma write_future
        loc from to val releasedm na ord tview mem1 mem2
        (MEM: Memory.closed mem1)
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem1)
        (CLOSED_RELM: Memory.closed_view releasedm mem1)
        (WRITE: Memory.add mem1 loc from to
                        (Message.message val (TView.write_released tview loc to releasedm ord) na)
                        mem2)
        (ALLOCED: ~ Memory.is_prealloced loc mem1):
    <<WF_TVIEW: TView.wf (TView.write_tview tview loc to ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.write_tview tview loc to ord) mem2>> /\
    <<CLOSED_RELEASED: Memory.closed_view (TView.write_released tview loc to releasedm ord) mem2>>.
  Proof.
    exploit write_future0; eauto. i. des. splits; eauto.
    - eapply write_closed_tview; eauto.
    - eapply write_closed_released; eauto.
  Qed.

  Lemma read_fence_future
        ord tview mem
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem):
    <<WF_TVIEW: TView.wf (TView.read_fence_tview tview ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.read_fence_tview tview ord) mem>>.
  Proof.
    splits.
    - econs; tac; try apply WF_TVIEW; condtac; try apply WF_TVIEW.
      + etrans; apply WF_TVIEW.
      + refl.
    - econs; tac; try apply CLOSED_TVIEW.
      condtac; try apply CLOSED_TVIEW.
  Qed.

  Lemma write_fence_future
        ord tview sc mem
        (MEM: Memory.closed mem)
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem)
        (CLOSED_SC: Memory.closed_view sc mem):
    <<WF_TVIEW: TView.wf (TView.write_fence_tview tview sc ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.write_fence_tview tview sc ord) mem>> /\
    <<CLOSED_SC: Memory.closed_view (TView.write_fence_sc tview sc ord) mem>>.
  Proof.
    splits; tac.
    - econs; tac; try apply WF_TVIEW.
      + repeat (try condtac; aggrtac; try apply WF_TVIEW).
        unfold TView.write_fence_sc. condtac; try congruence.
        etrans;[|apply View.join_r]. apply WF_TVIEW.
      + (try condtac; aggrtac; try apply WF_TVIEW).
    - econs; tac; try apply CLOSED_TVIEW.
      + unfold TView.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_TVIEW.
      + unfold TView.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_TVIEW.
      + unfold TView.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_TVIEW.
    - unfold TView.write_fence_sc.
      condtac; tac; try apply CLOSED_TVIEW.
  Qed.

  Lemma alloc_tview_future
        tview loc size mem1 tid mem2
        (CLOSED: Memory.closed mem1)
        (WELL_ALLOCED: Memory.well_alloced mem1)
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem1)
        (ALLOC: Memory.alloc mem1 tid size mem2 loc):
    <<WF_TVIEW: TView.wf (TView.alloc_tview tview loc size)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.alloc_tview tview loc size) mem2>>.
  Proof.
    splits.
    - econs; tac; try apply WF_TVIEW.
      + etrans. apply WF_TVIEW. apply View.join_l.
      + etrans. apply WF_TVIEW. apply View.join_l.
    - exploit TView.le_closed; eauto.
      { eapply Memory.alloc_messages_le; eauto. }
      i. inv CLOSED. econs; try apply x0.
      + apply Memory.join_closed_view; try apply x0.
        eapply Memory.alloc_view_singleton_closed_view; eauto.
      + apply Memory.join_closed_view; try apply x0.
        eapply Memory.alloc_view_singleton_closed_view; eauto.
  Qed.
End TViewFacts.

Ltac viewtac := TViewFacts.tac.
Ltac aggrtac := TViewFacts.aggrtac.

