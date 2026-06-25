Require Import CRIS.

From Stdlib Require Import FMapFacts.

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
Require Import Thread.

Set Implicit Arguments.


Module Threads.
  Definition syntax := IdentMap.t {lang: language & (Language.syntax lang)}.

  Definition t := IdentMap.t ({lang: language & (Language.state lang)} * Local.t).

  Definition init (s: syntax) size: t :=
    IdentMap.mapi
      (fun k s => (existT (projT1 s) (Language.init (projT1 s) (projT2 s)), Local.init k size))
      s.

  Definition is_terminal (ths: t): Prop :=
    forall tid lang st lc (FIND: IdentMap.find tid ths = Some (existT lang st, lc)),
      <<STATE: (Language.is_terminal lang) st>> /\
      <<THREAD: Local.is_terminal lc>>.

  Variant wf (ths: t) (gl: Global.t): Prop :=
  | wf_intro
      (DISJOINT:
         forall tid1 lang1 st1 lc1
           tid2 lang2 st2 lc2
           (HTID: tid1 <> tid2)
           (TH1: IdentMap.find tid1 ths = Some (existT lang1 st1, lc1))
           (TH2: IdentMap.find tid2 ths = Some (existT lang2 st2, lc2)),
           Local.disjoint lc1 lc2)
      (THREADS: forall tid lang st lc
                  (TH: IdentMap.find tid ths = Some (existT lang st, lc)),
          Local.wf lc gl)
      (PROMISES: forall loc (GET: Global.promises gl loc = true),
        exists tid lang st lc,
          (<<TH: IdentMap.find tid ths = Some (existT lang st, lc)>>) /\
          (<<GET: Local.promises lc loc = true>>))
      (FREEPROMISES: forall tbid (GET: Global.free_promises gl tbid = true),
        exists tid lang st lc,
          (<<TH: IdentMap.find tid ths = Some (existT lang st, lc)>>) /\
          (<<GET: Local.free_promises lc tbid = true>>))
      (HTID: forall tid lang st lc
              (TH: IdentMap.find tid ths = Some (existT lang st, lc)),
          Local.tid lc = tid)
  .

  Lemma init_wf syn size: wf (init syn size) (Global.init size).
  Proof.
    econs; ss.
    - i. unfold init in *. 
      rewrite IdentMap.Facts.mapi_o in TH1;
      rewrite IdentMap.Facts.mapi_o in TH2;
      try (by i; subst; ss).
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid1 syn); inv TH1.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid2 syn); inv TH2.
      econs; ss. econs. i.
      rewrite Memory.bot_get in GET1;
      rewrite Memory.bot_get in GET2.
      ss.
    - i. unfold init in *. 
      rewrite IdentMap.Facts.mapi_o in TH;
      try (by i; subst; ss).
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv TH.
      apply Local.init_wf.
    - i. unfold init in TH. rewrite IdentMap.Facts.mapi_o in TH; try (by i; subst; ss).
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv TH.
      unfold Local.init. ss.
  Qed.

  Lemma spawn_wf tid_new lang lc ths gl
      (WF : wf ths gl)
      (WF2 : ∃ tid, IdentMap.find tid ths = Some (lang, lc))
      (NIN : ¬ IdentMap.mem tid_new ths) :
    let lc_new := (lang, Local.mk (Local.tview lc) Promises.bot Memory.bot FreePromises.bot tid_new) in
    wf (IdentMap.add tid_new lc_new ths) gl.
  Proof.
    destruct WF2 as [tid FIND].
    intros lc_new; inv WF; econs; ss.
    { intros ???????? Hneq; rewrite ?IdentMap.gsspec; des_ifs; clarify; last by eapply DISJOINT.
      { case; intros -> <-; rewrite /= => /HTID; i; econs; ss; eauto using Memory.bot_disjoint; clarify. }
      { move => /HTID; intros <-; case; intros -> <-; econs; ss; clarify.
        symmetry; by eauto using Memory.bot_disjoint.
      }
    }
    { intros ????; rewrite IdentMap.gsspec; des_ifs; last by eapply THREADS.
      case; intros -> <-; econs; ss.
      { eapply THREADS; eauto. }
      { eapply THREADS; eauto. }
      { by apply Promises.bot_finite. }
      { by apply FreePromises.bot_finite. }
      { by apply Memory.bot_le. }
      { by apply Memory.bot_reserve_only. }
      { by apply Memory.bot_finite. }
    }
    { intros ? [tid_p [? [? [? [??]]]]]%PROMISES; exists tid_p; esplits; eauto.
      { rewrite IdentMap.gso; eauto; ii; apply NIN; rewrite IdentMap.mem_find; des_ifs; ss. }
    }
    { intros ? [tid_p [? [? [? [??]]]]]%FREEPROMISES; exists tid_p; esplits; eauto.
      { rewrite IdentMap.gso; eauto; ii; apply NIN; rewrite IdentMap.mem_find; des_ifs; ss. }
    }
    { intros ????; rewrite IdentMap.gsspec; des_ifs; last by apply HTID. case; intros -> <-; ss. }
  Qed.
  (* tids *)

  Definition tids (ths : t): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements ths).

  Lemma tids_o tid ths:
    IdentSet.mem tid (tids ths) = IdentMap.find tid ths.
  Proof.
    unfold tids. rewrite IdentMap.Facts.elements_o.
    induction (IdentMap.elements ths); ss. destruct a. s.
    rewrite IdentSet.Facts.add_b IHl.
    unfold IdentSet.Facts.eqb, IdentMap.Facts.eqb.
    repeat match goal with
           | [|- context[if ?c then true else false]] => destruct c
           end; ss; congruence.
  Qed.

  Lemma tids_add
        tid lang st lc ths:
    tids (IdentMap.add tid (existT lang st, lc) ths) = IdentSet.add tid (tids ths).
  Proof.
    apply IdentSet.ext. i.
    rewrite IdentSet.Facts.add_b ? tids_o.
    rewrite IdentMap.Facts.add_o. unfold IdentSet.Facts.eqb.
    repeat condtac; ss.
  Qed.

  Lemma is_terminal_spec ths:
    Threads.is_terminal ths <->
    forall tid lang st lc
      (TIDS: IdentSet.mem tid (tids ths))
      (FIND: IdentMap.find tid ths = Some (existT lang st, lc)),
      (Language.is_terminal lang) st /\ Local.is_terminal lc.
  Proof.
    unfold Threads.is_terminal. econs; i.
    - eapply H. eauto.
    - destruct (IdentMap.find tid ths) eqn:X; inv FIND.
      eapply H; eauto. rewrite tids_o X. ss.
  Qed.

  Lemma tids_find
        ths_src ths_tgt tid
        (TIDS: tids ths_src = tids ths_tgt):
    (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT lang_tgt st_tgt, lc_tgt)).
  Proof.
    split; i; des.
    - destruct (IdentSet.mem tid (tids ths_src)) eqn:MEM.
      + rewrite TIDS in MEM.
        rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
    - destruct (IdentSet.mem tid (tids ths_tgt)) eqn:MEM.
      + rewrite <- TIDS in MEM.
        rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
  Qed.
End Threads.


Module Configuration.
  Structure t := mk {
    threads: Threads.t;
    global: Global.t;
  }.

  Definition init (s: Threads.syntax) (size: list Z): t := mk (Threads.init s size) (Global.init size).

  Definition is_terminal (conf: t): Prop := Threads.is_terminal (threads conf).

  Variant wf (conf:t): Prop :=
  | wf_intro
      (WF: Threads.wf (threads conf) (global conf))
      (GL_WF: Global.wf (global conf))
  .

  Lemma init_wf syn size
    (SIZE: List.Forall (fun sz : Z => (0 <= sz)%Z) size):
    wf (init syn size).
  Proof.
    econs.
    - apply Threads.init_wf.
    - apply Global.init_wf. eauto.
  Qed.


  Variant step: forall (e: MachineEvent.t) (tid: Tid.t) (c1 c2: t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 th2 st3 lc3 gl3
      (HTID: IdentMap.find tid (threads c1) = Some (existT lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st1 lc1 (global c1)) th2)
      (STEP: Thread.step e th2 (Thread.mk _ st3 lc3 gl3))
      (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure ->
                   Thread.consistent (Thread.mk _ st3 lc3 gl3)):
      step (ThreadEvent.get_machine_event e) tid
           c1
           (mk (IdentMap.add tid (existT _ st3, lc3) (threads c1)) gl3)
  .
  #[global] Hint Constructors step: core.

  Variant normal_step (c1 c2: t): Prop :=
  | normal_step_intro
      e tid
      (STEP: step e tid c1 c2)
      (EVENT: e <> MachineEvent.failure)
  .
  #[global] Hint Constructors normal_step: core.

  Variant all_step (c1 c2: t): Prop :=
  | all_step_intro
      e tid
      (STEP: step e tid c1 c2)
  .
  #[global] Hint Constructors all_step: core.

  Variant opt_step: forall (e: MachineEvent.t) (tid: Tid.t) (c1 c2: t), Prop :=
  | step_none
      tid c:
      opt_step MachineEvent.silent tid c c
  | step_some
      e tid c1 c2
      (STEP: step e tid c1 c2):
      opt_step e tid c1 c2
  .
  #[global] Hint Constructors opt_step: core.

  Definition tau_step := union (step MachineEvent.silent).

  Variant steps_failure (c1: t): Prop :=
  | steps_failure_intro
      tid c2 c3
      (STEPS: rtc tau_step c1 c2)
      (FAILURE: step MachineEvent.failure tid c2 c3)
  .
  #[global] Hint Constructors steps_failure: core.

  Lemma inj_option_pair
        A B
        (a1 a2: A)
        (b1 b2: B)
        (EQ: Some (a1, b1) = Some (a2, b2)):
    a1 = a2 /\ b1 = b2.
  Proof.
    inv EQ. ss.
  Qed.

  Ltac simplify :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some _ = Some _ |- _] =>
             inv H
           | [H: (_, _) = (_, _) |- _] =>
             inv H
           | [H: existT ?P ?p _ = existT ?P ?p _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?P ?q _ |- _] =>
             apply eq_sigT_sig_eq in H; inv H
           end;
       ss; subst).

  Ltac simplify2 :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some (_, _) = Some (_, _) |- _] =>
             apply inj_option_pair in H; des
           | [H: existT ?P ?p _ = existT ?Q ?q _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?Q ?q _ |- _] =>
             exploit eq_sigT_fst; try exact H; i; subst
           end;
       ss; subst).

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.future (global c1) (global c2)>>.
  Proof.
    inv WF1. inv WF. inv STEP; s.
    exploit THREADS; ss; eauto. i.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    splits; try by etrans; eauto.
    econs; ss. econs; i.
    - simplify.
      + exploit THREADS; try apply TH1; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        auto.
      + exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        symmetry. auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - simplify.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      auto.
    - i. destruct (Local.promises lc3 loc) eqn:LGET.
      + exists tid, lang, st3, lc3. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.rtc_tau_step_promises_minus; try exact STEPS. s. i.
        exploit Thread.step_promises_minus; try exact STEP0. s. i.
        rewrite x2 in x1. eapply equal_f in x1.
        revert x1. unfold Promises.minus. erewrite GET, LGET. s. i.
        destruct (Global.promises (global c1) loc) eqn:GET1; ss.
        destruct (Local.promises lc1 loc) eqn:LGET1; ss.
        exploit PROMISES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congruence.
    - i. destruct (Local.free_promises lc3 tbid) eqn:LGET.
      + exists tid, lang, st3, lc3. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.rtc_tau_step_free_promises_minus; try exact STEPS. s. i.
        exploit Thread.step_free_promises_minus; try exact STEP0. s. i.
        rewrite x2 in x1. eapply equal_f in x1.
        revert x1. unfold FreePromises.minus. erewrite GET, LGET. s. i.
        destruct (Global.free_promises (global c1) tbid) eqn:GET1; ss.
        destruct (Local.free_promises lc1 tbid) eqn:LGET1; ss.
        exploit FREEPROMISES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congruence.
    - simplify.
      + exploit Thread.step_preserve; eauto. i. des.
        exploit Thread.rtc_tau_step_preserve; eauto. i. des.
        erewrite <- HTID; try exact HTID0. etrans; eauto.
      + eapply HTID; try exact TH.
    - inv GL_FUTURE. inv GL_FUTURE0. inv MEMORY. inv MEMORY0.
      econs; try etrans; eauto. econs; try etrans; eauto.
  Qed.

  Lemma opt_step_future
        e tid c1 c2
        (STEP: opt_step e tid c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.future (global c1) (global c2)>>.
  Proof.
    inv STEP.
    - splits; auto; try refl. inv WF1. inv GL_WF.
      econs; try refl. econs; eauto. econs; eauto; try refl.
    - eapply step_future; eauto.
  Qed.

  Lemma normal_step_future
        c1 c2
        (STEP: normal_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.future (global c1) (global c2)>>.
  Proof.
    inv STEP. eauto using step_future.
  Qed.

  Lemma all_step_future
        c1 c2
        (STEP: all_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.future (global c1) (global c2)>>.
  Proof.
    inv STEP. eauto using step_future.
  Qed.

  Lemma rtc_tau_step_future
        c1 c2
        (STEPS: rtc tau_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.future (global c1) (global c2)>>.
  Proof.
    induction STEPS; i.
    - splits; auto; try refl. eapply Global.future_refl. eapply WF1.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; try etrans; eauto.
      eapply Global.future_trans; eauto.
  Qed.

  Lemma rtc_normal_step_future
        c1 c2
        (STEPS: rtc normal_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.future (global c1) (global c2)>>.
  Proof.
    induction STEPS; i.
    - splits; auto; try refl. eapply Global.future_refl. eapply WF1.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; try etrans; eauto.
      eapply Global.future_trans; eauto.
  Qed.

  Lemma rtc_all_step_future
        c1 c2
        (STEPS: rtc all_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.future (global c1) (global c2)>>.
  Proof.
    induction STEPS; i.
    - splits; auto; try refl. eapply Global.future_refl. eapply WF1.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; try etrans; eauto.
      eapply Global.future_trans; eauto.
  Qed.

  Lemma step_strong_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.strong_future (global c1) (global c2)>>
    \/
    <<FAILURE: steps_failure c1>>
  .
  Proof.
    inv WF1. inv WF. inv STEP; s.
    exploit THREADS; ss; eauto. i.
    destruct (classic (Thread.steps_failure (Thread.mk _ st1 lc1 c1.(global)))).
    { inv H. destruct th3. right. econs.
      { refl. }
      rewrite <- EVENT_FAILURE. econs.
      { eauto. }
      { eauto. }
      { eauto. }
      { rewrite EVENT_FAILURE. ss. }
    }
    left.
    exploit Thread.rtc_tau_step_strong_future; eauto. s. i. des; ss.
    exploit Thread.step_strong_future; eauto. s. i. des.
    2:{ exfalso. eapply H. eapply Thread.steps_failure_intro; eauto. }
    splits; cycle 1.
    { eapply Global.strong_future_trans; eauto. }
    econs; ss. econs; i.
    - simplify.
      + exploit THREADS; try apply TH1; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        auto.
      + exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        symmetry. auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - simplify.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      auto.
    - i. destruct (Local.promises lc3 loc) eqn:LGET.
      + exists tid, lang, st3, lc3. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.rtc_tau_step_promises_minus; try exact STEPS. s. i.
        exploit Thread.step_promises_minus; try exact STEP0. s. i.
        rewrite x2 in x1. eapply equal_f in x1.
        revert x1. unfold Promises.minus. erewrite GET, LGET. s. i.
        destruct (Global.promises (global c1) loc) eqn:GET1; ss.
        destruct (Local.promises lc1 loc) eqn:LGET1; ss.
        exploit PROMISES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congruence.
    - i. destruct (Local.free_promises lc3 tbid) eqn:LGET.
      + exists tid, lang, st3, lc3. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.rtc_tau_step_free_promises_minus; try exact STEPS. s. i.
        exploit Thread.step_free_promises_minus; try exact STEP0. s. i.
        rewrite x2 in x1. eapply equal_f in x1.
        revert x1. unfold FreePromises.minus. erewrite GET, LGET. s. i.
        destruct (Global.free_promises (global c1) tbid) eqn:GET1; ss.
        destruct (Local.free_promises lc1 tbid) eqn:LGET1; ss.
        exploit FREEPROMISES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congruence.
    - destruct (classic (tid0 = tid)).
      { subst. rewrite IdentMap.gss in TH. clarify. eapply HTID in HTID0.
        exploit Thread.rtc_tau_step_preserve; eauto. i. des. ss.
        exploit Thread.step_preserve; eauto. i. des. ss.
        etrans; eauto. etrans; eauto.
      }
      { rewrite IdentMap.gso in TH; eauto. }
  Qed.

  Lemma opt_step_strong_future
        e tid c1 c2
        (STEP: opt_step e tid c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.strong_future (global c1) (global c2)>>
    \/
    <<FAILURE: steps_failure c1>>
  .
  Proof.
    inv STEP.
    - left. splits; auto. eapply Global.strong_future_refl. eapply WF1.
    - eapply step_strong_future; eauto.
  Qed.

  Lemma normal_step_strong_future
        c1 c2
        (STEP: normal_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.strong_future (global c1) (global c2)>>
    \/
    <<FAILURE: steps_failure c1>>
  .
  Proof.
    inv STEP. eauto using step_strong_future.
  Qed.

  Lemma rtc_tau_step_strong_future
        c1 c2
        (STEPS: rtc tau_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<GL_FUTURE: Global.strong_future (global c1) (global c2)>>
    \/
    <<FAILURE: steps_failure c1>>
  .
  Proof.
    induction STEPS; i.
    - left. splits; auto. eapply Global.strong_future_refl. eapply WF1.
    - inv H.
      exploit step_strong_future; eauto. i. des.
      2:{ right. auto. }
      exploit IHSTEPS; eauto. i. des.
      { left. splits; eauto. eapply Global.strong_future_trans; eauto. }
      { right. inv FAILURE. econs.
        { econs 2; eauto. econs; eauto. }
        { eauto. }
      }
  Qed.
End Configuration.
