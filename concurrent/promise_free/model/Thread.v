Require Import CRIS.

Require Import Basic.
Require Import Loc.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Language.
Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Global.
Require Import Local.
Require Import Val.

Set Implicit Arguments.


Variant tau T (step: forall (e:ThreadEvent.t) (th1 th2:T), Prop) (th1 th2:T): Prop :=
| tau_intro
    e
    (TSTEP: step e th1 th2)
    (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
.
#[export] Hint Constructors tau: core.

Variant union E T (step: forall (e:E) (th1 th2:T), Prop) (th1 th2:T): Prop :=
| union_intro
    e
    (USTEP: step e th1 th2)
.
#[export] Hint Constructors union: core.

Variant pstep E T (step: forall (e: E) (th1 th2: T), Prop) (P: E -> Prop) (th1 th2: T): Prop :=
| pstep_intro
    e
    (STEP: step e th1 th2)
    (EVENT: P e)
.
#[export] Hint Constructors pstep: core.

Lemma tau_mon T (step1 step2: forall (e:ThreadEvent.t) (th1 th2:T), Prop)
      (STEP: step1 <3= step2):
  tau step1 <2= tau step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma union_mon E T (step1 step2: forall (e:E) (th1 th2:T), Prop)
      (STEP: step1 <3= step2):
  union step1 <2= union step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma pstep_mon E T (step1 step2: forall (e:E) (th1 th2:T), Prop) P1 P2
      (STEP: step1 <3= step2)
      (P: P1 <1= P2):
  pstep step1 P1 <2= pstep step2 P2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma tau_union: tau <4= (@union ThreadEvent.t).
Proof.
  ii. inv PR. econs. eauto.
Qed.

Lemma pstep_union E T step P:
  @pstep E T step P <2= @union E T step.
Proof.
  i. inv PR. eauto.
Qed.

Module Thread.
  Section Thread.
    Variable (lang: language).

    Structure t := mk {
      state: (Language.state lang);
      local: Local.t;
      global: Global.t;
    }.

    Variant step: forall (e: ThreadEvent.t) (th1 th2: t), Prop :=
    | step_internal
        e st lc1 gl1 lc2 gl2
        (LOCAL: Local.internal_step e lc1 gl1 lc2 gl2):
      step e (mk st lc1 gl1) (mk st lc2 gl2)
    | step_program
        e st1 lc1 gl1 st2 lc2 gl2
        (STATE: Language.step lang (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: Local.program_step e lc1 gl1 lc2 gl2):
      step e (mk st1 lc1 gl1) (mk st2 lc2 gl2)
    .
    Hint Constructors step: core.

    Definition tau_step := tau step.
    Hint Unfold tau_step: core.

    Definition all_step := union step.
    Hint Unfold all_step: core.

    Variant opt_step: forall (e:ThreadEvent.t) (th1 th2:t), Prop :=
      | step_none
          th:
        opt_step ThreadEvent.silent th th
      | step_some
          e th1 th2
          (STEP: step e th1 th2):
        opt_step e th1 th2
    .
    Hint Constructors opt_step: core.

    Definition step_star (e:ThreadEvent.t) (th1 th2:t) :=
      exists th1',
        (<<STEPS: rtc tau_step th1 th1'>>) /\
        (<<STEP_OPT: opt_step e th1' th2>>).

    Variant internal_step: forall (th1 th2: t), Prop :=
    | interal_step_intro
        e st lc1 gl1 lc2 gl2
        (LOCAL: Local.internal_step e lc1 gl1 lc2 gl2):
      internal_step (mk st lc1 gl1) (mk st lc2 gl2)
    .
    Hint Constructors internal_step: core.

    Variant program_step: forall (e: ThreadEvent.t) (th1 th2: t), Prop :=
    | program_step_intro
        e st1 lc1 gl1 st2 lc2 gl2
        (STATE: Language.step lang (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: Local.program_step e lc1 gl1 lc2 gl2):
      program_step e (mk st1 lc1 gl1) (mk st2 lc2 gl2)
    .
    Hint Constructors program_step: core.

    Lemma tau_opt_tau
          th1 th2 th3 e
          (STEPS: rtc tau_step th1 th2)
          (STEP: opt_step e th2 th3)
          (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
      rtc tau_step th1 th3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto.
    Qed.

    Lemma tau_opt_all
          th1 th2 th3 e
          (STEPS: rtc tau_step th1 th2)
          (STEP: opt_step e th2 th3):
      rtc all_step th1 th3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto. i.
        econs 2; eauto.
        inv H. econs. eauto.
    Qed.


    (* consistency *)

    Variant cap (th th_cap: t): Prop :=
    | cap_intro
      (STATE: state th_cap = state th)
      (LOCAL: local th_cap = local th)
      (GLOBAL: Global.cap (global th) (global th_cap))
    .
    Hint Constructors cap: core.
    
    Definition cap_of (th: t): t :=
      mk (state th) (local th) (Global.cap_of (global th)).

    Lemma cap_of_cap gl:
      cap gl (cap_of gl).
    Proof.
      econs; ss.
      apply Global.cap_of_cap.
    Qed.

    Variant state_future (th th': t): Prop :=
    | state_future_intro
        (STATE: state th' = state th)
        (LOCAL: local th' = local th)
        (GLOBAL: Global.state_future (global th) (global th'))
        (NEXTBID: Memory.next_bid (Global.memory (global th)) (Local.tid (local th)) =
                  Memory.next_bid (Global.memory (global th')) (Local.tid (local th')))
    .

    Variant steps_failure (th1: t): Prop :=
      | steps_failure_intro
          e th2 th3
          (STEPS: rtc tau_step th1 th2)
          (STEP_FAILURE: step e th2 th3)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    .

    Variant consistent (th: t): Prop :=
      | consistent_failure
          (FAILURE: steps_failure (cap_of th))
      | consistent_fulfill
          th2
          (STEPS: rtc tau_step (cap_of th) th2)
          (PROMISES: Local.promises (Thread.local th2) = Promises.bot)
          (PROMISESFREE: Local.free_promises (Thread.local th2) = FreePromises.bot)
    .

    Lemma cap_wf
          th th_cap
          (LC_WF: Local.wf (local th) (global th))
          (GL_WF: Global.wf (global th))
          (CAP: cap th th_cap)
          (WELL_ALLOC: Memory.well_alloced (Global.memory (global th_cap))):
      (<<LC_WF_CAP: Local.wf (local th_cap) (global th_cap)>>) /\
      (<<GL_WF_CAP: Global.wf (global th_cap)>>).
    Proof.
      inv CAP. rewrite LOCAL.
      exploit Local.cap_wf; eauto.
      exploit Global.cap_wf; eauto.
    Qed.

    Lemma cap_of_wf
          th
          (LC_WF: Local.wf (local th) (global th))
          (GL_WF: Global.wf (global th)):
      (<<LC_WF_CAP: Local.wf (local (cap_of th)) (global (cap_of th))>>) /\
      (<<GL_WF_CAP: Global.wf (global (cap_of th))>>).
    Proof.
      eapply cap_wf; eauto.
      eapply cap_of_cap; eauto.
      eapply Memory.cap_of_well_alloced. eapply GL_WF.
    Qed.

    (* step_preserve *)
    Lemma step_preserve
          e th1 th2
          (STEP: step e th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Local.tid (local th1) <> tid ->
                        Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      inv STEP; ss.
      - exploit Local.internal_step_preserve; eauto. i. des. esplits; eauto.
      - eauto using Local.program_step_preserve.
    Qed.
    
    Lemma opt_step_preserve
          e th1 th2
          (STEP: opt_step e th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Local.tid (local th1) <> tid ->
                        Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      inv STEP; eauto using step_preserve.
    Qed.

    Lemma rtc_all_step_preserve
          th1 th2
          (STEP: rtc all_step th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Local.tid (local th1) <> tid ->
                        Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      induction STEP; i.
      - splits; ss; try refl.
      - inv H. exploit step_preserve; eauto. i. des.
        splits; ss; try by (etrans; eauto).
        rewrite HTID in NEXTBID0. i. erewrite NEXTBID0; eauto.
    Qed.

    Lemma rtc_tau_step_preserve
          th1 th2
          (STEP: rtc tau_step th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Local.tid (local th1) <> tid ->
                        Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      apply rtc_all_step_preserve; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma internal_step_preserve
          th1 th2
          (STEP: internal_step th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      inv STEP; ss. eauto using Local.internal_step_preserve.
    Qed.

    Lemma rtc_internal_step_preserve
          th1 th2
          (STEP: rtc internal_step th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Local.tid (local th1) <> tid ->
                        Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      induction STEP; i.
      - splits; ss; try refl.
      - inv H. exploit internal_step_preserve; eauto. i. instantiate (1 := st) in x0. des.
        splits; ss; try by (etrans; eauto).
        rewrite HTID in NEXTBID0. i. erewrite NEXTBID0; eauto.
    Qed.

    Lemma program_step_preserve
          e th1 th2
          (STEP: program_step e th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Local.tid (local th1) <> tid ->
                        Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      inv STEP; ss. eauto using Local.program_step_preserve.
    Qed.

    Lemma rtc_program_step_preserve
          th1 th2
          (STEP: rtc (tau program_step) th1 th2):
      <<HTID: Local.tid (local th2) = Local.tid (local th1)>> /\
      <<NEXTBID: forall tid, Local.tid (local th1) <> tid ->
                        Memory.next_bid (Global.memory (global th2)) tid =
                        Memory.next_bid (Global.memory (global th1)) tid>>.
    Proof.
      induction STEP; i.
      - splits; ss; try refl.
      - inv H. exploit program_step_preserve; eauto. i. des.
        splits; ss; try by (etrans; eauto).
        rewrite HTID in NEXTBID0. i. erewrite NEXTBID0; eauto.
    Qed.

    (* step_future *)

    Lemma step_future
          e th1 th2
          (STEP: step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; ss.
      - eauto using Local.internal_step_future.
      - eauto using Local.program_step_future.
    Qed.

    Lemma opt_step_future
          e th1 th2
          (STEP: opt_step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; eauto using step_future.
      esplits; eauto; try refl.
      inv GL_WF1. econs; try refl. econs; ss. eapply Memory.messages_le_PreOrder.
    Qed.

    Lemma rtc_all_step_future
          th1 th2
          (STEP: rtc all_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      revert LC_WF1. induction STEP; i.
      - splits; ss; try refl.
        inv GL_WF1. econs; try refl. econs; ss. eapply Memory.messages_le_PreOrder.
      - inv H. exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; try by (etrans; eauto).
        + inv GL_FUTURE. inv GL_FUTURE0. inv MEMORY. inv MEMORY0.
          econs; eauto. econs; eauto. eapply Memory.messages_le_PreOrder; eauto.
    Qed.

    Lemma rtc_tau_step_future
          th1 th2
          (STEP: rtc tau_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future  (global th1) (global th2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma internal_step_future
          th1 th2
          (STEP: internal_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; ss. eauto using Local.internal_step_future.
    Qed.

    Lemma rtc_internal_step_future
          th1 th2
          (STEP: rtc internal_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      revert LC_WF1. induction STEP; i.
      - splits; ss; try refl.
        inv GL_WF1. econs; try refl. econs; ss. eapply Memory.messages_le_PreOrder.
      - inv H. exploit internal_step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; try by (etrans; eauto).
        + inv GL_FUTURE. inv GL_FUTURE0. inv MEMORY. inv MEMORY0.
          econs; eauto. econs; eauto. eapply Memory.messages_le_PreOrder; eauto.
    Qed.

    Lemma program_step_future
          e th1 th2
          (STEP: program_step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; ss. eauto using Local.program_step_future.
    Qed.

    Lemma rtc_program_step_future
          th1 th2
          (STEP: rtc (tau program_step) th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      revert LC_WF1. induction STEP; i.
      - splits; ss; try refl.
        inv GL_WF1. econs; try refl. econs; ss. eapply Memory.messages_le_PreOrder.
      - inv H. exploit program_step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; try by (etrans; eauto).
        + inv GL_FUTURE. inv GL_FUTURE0. inv MEMORY. inv MEMORY0.
          econs; eauto. econs; eauto. eapply Memory.messages_le_PreOrder; eauto.
    Qed.

    (* step_disjoint *)

    Lemma step_disjoint
          e th1 th2 lc
          (STEP: step e th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF_O: Local.wf lc (global th1))
          (GL_WF: Global.wf (global th1))
          (LC_WF: Local.wf (local th1) (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      inv STEP.
      - eapply Local.internal_step_disjoint; eauto.
      - eapply Local.program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint
          e th1 th2 lc
          (STEP: opt_step e th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF_O: Local.wf lc (global th1))
          (GL_WF: Global.wf (global th1))
          (LC_WF: Local.wf (local th1) (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          th1 th2 lc
          (STEP: rtc all_step th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF_O: Local.wf lc (global th1))
          (GL_WF: Global.wf (global th1))
          (LC_WF: Local.wf (local th1) (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      revert DISJOINTH1 LC_WF. induction STEP; eauto. i.
      inv H. exploit step_disjoint; eauto. i. des.
      exploit step_future; eauto. i. des. eauto.
    Qed.

    Lemma rtc_tau_step_disjoint
          th1 th2 lc
          (STEP: rtc tau_step th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF_O: Local.wf lc (global th1))
          (GL_WF: Global.wf (global th1))
          (LC_WF: Local.wf (local th1) (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma program_step_promises
          e th1 th2
          (STEP: Thread.step e th1 th2)
          (EVENT: ThreadEvent.is_program e):
      Promises.le (Local.promises (local th2)) (Local.promises (local th1)) /\
      Promises.le (Global.promises (global th2)) (Global.promises (global th1)).
    Proof.
      inv STEP; try by (inv LOCAL; ss).
      eapply Local.program_step_promises; eauto.
    Qed.

    Lemma step_promises_minus
          e th1 th2
          (STEP: step e th1 th2):
      Promises.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      Promises.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
    Proof.
      inv STEP; s.
      - eapply Local.internal_step_promises_minus; eauto.
      - eapply Local.program_step_promises_minus; eauto.
    Qed.

    Lemma rtc_all_step_promises_minus
          th1 th2
          (STEPS: rtc all_step th1 th2):
      Promises.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      Promises.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
    Proof.
      induction STEPS; ss. inv H.
      exploit step_promises_minus; eauto. i. congruence.
    Qed.

    Lemma rtc_tau_step_promises_minus
          th1 th2
          (STEPS: rtc tau_step th1 th2):
      Promises.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      Promises.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
    Proof.
      apply rtc_all_step_promises_minus.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.

    Lemma program_step_free_promises
          e th1 th2
          (STEP: Thread.step e th1 th2)
          (EVENT: ThreadEvent.is_program e):
      FreePromises.le (Local.free_promises (local th2)) (Local.free_promises (local th1)) /\
      FreePromises.le (Global.free_promises (global th2)) (Global.free_promises (global th1)).
    Proof.
      inv STEP; try by (inv LOCAL; ss).
      eapply Local.program_step_free_promises; eauto.
    Qed.

    Lemma step_free_promises_minus
          e th1 th2
          (STEP: step e th1 th2):
      FreePromises.minus (Global.free_promises (Thread.global th1)) (Local.free_promises (Thread.local th1)) =
      FreePromises.minus (Global.free_promises (Thread.global th2)) (Local.free_promises (Thread.local th2)).
    Proof.
      inv STEP; s.
      - eapply Local.internal_step_free_promises_minus; eauto.
      - eapply Local.program_step_free_promises_minus; eauto.
    Qed.

    Lemma rtc_all_step_free_promises_minus
          th1 th2
          (STEPS: rtc all_step th1 th2):
      FreePromises.minus (Global.free_promises (Thread.global th1)) (Local.free_promises (Thread.local th1)) =
      FreePromises.minus (Global.free_promises (Thread.global th2)) (Local.free_promises (Thread.local th2)).
    Proof.
      induction STEPS; ss. inv H.
      exploit step_free_promises_minus; eauto. i. congruence.
    Qed.

    Lemma rtc_tau_step_free_promises_minus
          th1 th2
          (STEPS: rtc tau_step th1 th2):
      FreePromises.minus (Global.free_promises (Thread.global th1)) (Local.free_promises (Thread.local th1)) =
      FreePromises.minus (Global.free_promises (Thread.global th2)) (Local.free_promises (Thread.local th2)).
    Proof.
      apply rtc_all_step_free_promises_minus.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.

    (* step_strong_future *)

    Lemma step_strong_future
          e th1 th2
          (STEP: step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.strong_future (global th1) (global th2)>>
      \/
      exists e_race th2',
        <<STEP: step e_race th1 th2'>> /\
        <<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e>> /\
        <<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>
    .
    Proof.
      inv STEP; ss.
      - eauto using Local.internal_step_strong_future.
      - hexploit Local.program_step_strong_future; eauto. i. des.
        { left. esplits; eauto. }
        { right. exists e_race. esplits; eauto. econs 2; eauto.
          rewrite EVENT. eauto.
        }
    Qed.

    Lemma opt_step_strong_future
          e th1 th2
          (STEP: opt_step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.strong_future (global th1) (global th2)>>
      \/
      exists e_race th2',
        <<STEP: step e_race th1 th2'>> /\
        <<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e>> /\
        <<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>
    .
    Proof.
      inv STEP; eauto using step_strong_future.
      left. esplits; eauto; try refl. eapply Global.strong_future_refl; eauto.
    Qed.

    Lemma rtc_tau_step_strong_future
          th1 th2
          (STEP: rtc tau_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.strong_future (global th1) (global th2)>>
          \/
      <<FAILURE: steps_failure th1>>
    .
    Proof.
      revert LC_WF1. induction STEP; i.
      - left. splits; ss; try refl. eapply Global.strong_future_refl; eauto.
      - inv H. exploit step_strong_future; eauto. i. des.
        2:{ right. repeat red. econs; [refl| |]; eauto. }
        exploit IHSTEP; eauto. i. des.
        { left. splits; auto; try by (etrans; eauto).
          eapply Global.strong_future_trans; eauto.
        }
        { inv FAILURE. right. econs.
          { econs 2.
            { econs; eauto. }
            { eauto. }
          }
          { eauto. }
          { eauto. }
        }
    Qed.

    (* internal and program step *)

    Lemma internal_step_tau_thread_step
          th1 th2
          (STEP: internal_step th1 th2)
      :
      tau_step th1 th2.
    Proof.
      inv STEP. econs 1; eauto. inv LOCAL; ss.
    Qed.

    Lemma program_step_thread_step
          e th1 th2
          (STEP: program_step e th1 th2)
      :
      step e th1 th2.
    Proof.
      inv STEP. econs 2; eauto.
    Qed.

    Lemma rtc_internal_step_rtc_tau_thread_step
          th1 th2
          (STEPS: rtc internal_step th1 th2)
      :
      rtc tau_step th1 th2.
    Proof.
      induction STEPS; eauto. econs 2; [|eauto].
      eapply internal_step_tau_thread_step; eauto.
    Qed.

    Lemma rtc_tau_program_step_rtc_tau_thread_step
          th1 th2
          (STEPS: rtc (tau program_step) th1 th2)
      :
      rtc tau_step th1 th2.
    Proof.
      induction STEPS; eauto. econs 2; [|eauto].
      inv H. econs; eauto. eapply program_step_thread_step; eauto.
    Qed.

    Definition drop_prm (th: t): t :=
      let (st, lc, gl) := th in
      let (tview, prm, rsv, fprm, tid) := lc in
      let (sc, gprm, gfprm, mem) := gl in
      mk st (Local.mk tview Promises.bot rsv fprm tid)
        (Global.mk sc (Promises.minus gprm prm) gfprm mem).

    Lemma drop_prm_wf
          th
          (LC_WF: Local.wf (local th) (global th))
          (GL_WF: Global.wf (global th)):
      (<<LC_WF_CAP: Local.wf (local (drop_prm th)) (global (drop_prm th))>>) /\
      (<<GL_WF_CAP: Global.wf (global (drop_prm th))>>).
    Proof.
      destruct th as [st [tview prm rsv fprm tid] [sc gprm gfprm mem]]. inv LC_WF. inv GL_WF. ss.
      split; econs; eauto; ss. eapply Promises.bot_finite.
    Qed.

    Lemma step_drop e th1 th2
          (STEP: step e th1 th2)
          (EVENT: ThreadEvent.is_pf e):
      step e (drop_prm th1) (drop_prm th2).
    Proof.
      destruct th1 as [st1 [tview1 prm1 rsv1 fprm1 tid1] [sc1 gprm1 gfprm1 mem1]].
      inv STEP; inv LOCAL; inv EVENT; ss.
      - inv LOCAL0. ss. econs. econs 3. econs; eauto.
      - econs 2; ss.
      - inv LOCAL0. ss. econs; ss. econs; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto. econs; eauto. ss.
        f_equal. erewrite <- Promises.fulfill_minus; eauto.
      - inv LOCAL1. inv LOCAL2. ss. econs; ss. econs; eauto. econs; eauto. ss.
        f_equal. erewrite <- Promises.fulfill_minus; eauto.
      - inv LOCAL1. inv LOCAL2. ss. econs; ss. econs; eauto.
        + inv COMPARE. ss. econs. ss. econs. inv CMP. econs; eauto.
        + econs; eauto. ss. f_equal. erewrite <- Promises.fulfill_minus; eauto.
      - inv LOCAL1. ss. econs; ss. econs; eauto. inv COMPARE.
        + rewrite {2} H2. econs.
        + econs. inv CMP.
          * econs; eauto.
          * econs 2; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto. econs; eauto. ss.
        erewrite Promises.fulfills_minus; eauto. eapply Promises.fulfills_refl.
      - inv LOCAL0.
        + econs; eauto.
        + econs; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto. econs; ss. inv RACE.
        + econs; eauto. eapply Promises.minus_true_spec; eauto.
        + econs; eauto.
      - inv LOCAL0. ss. econs; ss. econs; eauto. econs; ss. inv RACE.
        + econs; eauto. eapply Promises.minus_true_spec; eauto.
        + econs; eauto.
      - inv LOCAL0; eauto. ss. econs; ss. econs; eauto. econs; ss. inv RACE.
        + econs; eauto. eapply Promises.minus_true_spec; eauto.
        + econs; eauto.
      - inv LOCAL0; eauto. ss. econs; ss. econs; eauto. econs; ss. inv RACE.
        + econs; eauto. eapply Promises.minus_true_spec; eauto.
        + econs; eauto.
      - inv LOCAL0; eauto. ss. econs; ss. econs; eauto. des. econs; eauto. esplits; eauto. inv RACE0.
        + econs; eauto. eapply Promises.minus_true_spec; eauto.
        + econs; eauto.
      - econs; eauto. econs. inv RACE; try (by econs; eauto).
      - econs; eauto. econs. inv RACE; try (by econs; eauto).
      - econs; eauto. econs. inv RACE; try (by econs; eauto).
      - econs; eauto. econs. inv RACE; try (by econs; eauto).
      - inv LOCAL0; ss. inv LOCAL; ss. econs; eauto. econs. econs; eauto.
        inv COMPARE; try (by econs; eauto). econs. inv CMP.
        + econs; eauto. inv RACE; try (by econs; eauto).
        + econs 2; eauto. inv RACE; try (by econs; eauto).
      - econs; eauto. econs. inv LOCAL0; ss.
        + econs; eauto. des; eauto. left. esplits; eauto. inv RACE0; try (by econs; eauto).
        + econs 2; eauto.
      - econs; eauto. econs. inv LOCAL0; ss.
        + econs; eauto. inv RACE; try (by econs; eauto).
        + econs 2; eauto. inv RACE; try (by econs; eauto).
    Qed.

    Lemma rtc_step_drop th1 th2
          (STEPS: rtc (pstep step ThreadEvent.is_pf) th1 th2):
      rtc (pstep step ThreadEvent.is_pf) (drop_prm th1) (drop_prm th2).
    Proof.
      induction STEPS; eauto. econs; eauto. inv H. exploit step_drop; eauto.
    Qed.

    Lemma step_drop_inv e th1 dth2
          (STEP: step e (drop_prm th1) dth2)
          (EVENT: ThreadEvent.is_pf e)
          (EVENT1: ~ ThreadEvent.is_sc e):
      exists th2, step e th1 th2 /\ drop_prm th2 = dth2.
    Proof.
      destruct th1 as [st1 [tview1 prm1 rsv1 fprm1 tid1] [sc1 gprm1 gfprm1 mem1]].
      destruct dth2 as [st2 [tview2 prm2 rsv2 fprm2 tid2] [sc2 gprm2 gfprm2 mem2]].
      inv STEP; inv LOCAL; inv EVENT; ss.
      - inv LOCAL0. ss. esplits; eauto.
      - esplits; eauto.
      - inv LOCAL0. ss. esplits; eauto.
      - inv LOCAL0. ss. esplits; eauto. ss.
        exploit Promises.fulfill_bot; eauto. i. des. subst. eauto.
      - inv LOCAL1. inv LOCAL2. ss. esplits; eauto.
        + econs 2; eauto.
        + ss. exploit Promises.fulfill_bot; eauto. i. des. subst. eauto.
      - inv LOCAL1. inv LOCAL2. ss. esplits; eauto.
        + econs 2; eauto. econs; eauto. ss. inv COMPARE; try (by econs; eauto).
          inv CMP; try (by econs; eauto).
        + ss. exploit Promises.fulfill_bot; eauto. i. des. subst. eauto.
      - inv LOCAL1. ss. esplits; eauto.
        + econs 2; eauto. econs; eauto. ss. inv COMPARE.
          * rewrite {2} H2. econs; eauto.
          * econs. inv CMP; try (by econs; eauto).
        + ss.
      - inv LOCAL0. ss. esplits; eauto.
        + econs 2; eauto. econs; eauto. econs; eauto. i. ss.
        + ss.
      - esplits; eauto.
      - inv LOCAL0. ss. esplits; eauto.
      - inv LOCAL0. ss. esplits; eauto.
        + econs 2; eauto. econs; eauto. econs; eauto. ss. eapply Promises.fulfills_refl.
        + hexploit Promises.fulfills_bot; eauto. i. des. subst. ss.
      - inv LOCAL0; esplits; eauto.
      - inv LOCAL0. ss. esplits; eauto.
        + econs 2; eauto. econs; eauto. econs; eauto. inv RACE; try (by econs; eauto). ss.
          rewrite Promises.minus_true_spec in GET. des. econs; eauto.
        + ss.
      - inv LOCAL0. esplits; eauto.
        + econs 2; eauto. econs. econs; eauto. inv RACE; try (by econs; eauto). ss.
          rewrite Promises.minus_true_spec in GET. des. econs; eauto.
        + ss.
      - inv LOCAL0; esplits; eauto.
        + econs 2; eauto. econs. econs; eauto. inv RACE; try (by econs; eauto). ss.
          rewrite Promises.minus_true_spec in GET. des. econs; eauto.
        + ss.
      - inv LOCAL0; esplits; eauto.
        + econs 2; eauto. econs. econs; eauto. inv RACE; try (by econs; eauto). ss.
          rewrite Promises.minus_true_spec in GET. des. econs; eauto.
        + ss.
      - inv LOCAL0; esplits; eauto.
        + econs 2; eauto. econs. econs; eauto. des. esplits; eauto. instantiate (1 := to).
          inv RACE0; try (by econs; eauto). ss.
          rewrite Promises.minus_true_spec in GET. des. econs; eauto.
        + ss.
      - esplits; eauto.
        + econs 2; eauto. econs. inv RACE; try (by econs; eauto).
        + ss.
      - esplits; eauto.
        + econs 2; eauto. econs. inv RACE; try (by econs; eauto).
        + ss.
      - esplits; eauto.
        + econs 2; eauto. econs. inv RACE; try (by econs; eauto).
        + ss.
      - esplits; eauto.
        + econs 2; eauto. econs. inv RACE; try (by econs; eauto).
        + ss.
      - inv LOCAL0. inv LOCAL. esplits; eauto.
        + econs 2; eauto. econs. econs; eauto. ss. inv COMPARE; econs; eauto. inv CMP.
          * econs; eauto. inv RACE; try (by econs; eauto).
          * econs 2; eauto. inv RACE; try (by econs; eauto).
        + ss.
      - inv LOCAL0; esplits; eauto.
        + econs 2; eauto. econs. econs; eauto. des; eauto.
          left. esplits; eauto. inv RACE0; try (by econs; eauto).
        + ss.
      - esplits; eauto.
        + econs 2; eauto. econs; eauto. inv LOCAL0.
          * econs; eauto. inv RACE; try (by econs; eauto).
          * econs 2; eauto. inv RACE; try (by econs; eauto).
        + ss.
    Qed.
    
    Lemma rtc_step_drop_inv th1 dth2
          (STEPS: rtc (pstep step (fun e => ThreadEvent.is_pf e /\ ~ ThreadEvent.is_sc e))
                    (drop_prm th1) dth2):
      exists th2, rtc (pstep step (fun e => ThreadEvent.is_pf e /\ ~ ThreadEvent.is_sc e)) th1 th2 /\
             drop_prm th2 = dth2.
    Proof.
      remember (drop_prm th1) as dth1. revert th1 Heqdth1. induction STEPS; eauto.
      i. inv H. des. exploit step_drop_inv; eauto. i. des. exploit IHSTEPS; eauto. i. des.
      esplits; try eapply x3. econs; eauto.
    Qed.

  End Thread.
End Thread.
#[export] Hint Constructors Thread.step: core.
#[export] Hint Constructors Thread.opt_step: core.
#[export] Hint Constructors Thread.steps_failure: core.
#[export] Hint Constructors Thread.consistent: core.

