Require Import CRIS.common.CRIS.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.system Require Import SystemHeader SystemA SystemTactics.
From CRIS.promise_free.elimination_stack Require Import StackHeader StackA StackI.
From CRIS.helping Require Import HelpingTactics HelpingFacts.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG,
    _SYS: !sysGS, _STACK: !stackG, _HELP: !helpingGS, !schGS}.
  Local Existing Instance stack_token_inG.
  Context (mn : string) (sp_user sp : specmap).
  Context (Hsys : (SystemA.sp sp_user (↑stackN)) ⊆ sp).

  Local Definition SysF := CFilter.filter (Helping.exports mn)
    (SystemA.t sp_user (↑stackN) sp).
  Local Definition SchF := CFilter.filter (Helping.exports mn) SchI.t.
  Local Definition MA :=
    ((StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOn.t mn StackM.jobCode) ★ SysF) ★ SchF.
  Local Definition MI :=
    ((CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn) ★ SysF) ★ SchF.
  Local Notation Ist :=
    (IstProd (IstSB [mn] (IstHelp IstTrue ⊤)) IstEq).

  Local Lemma push_postcond_irrel value γs tid stid V V' :
    postcond StackM.push_spec (value, γs, tid, stid, V) =
    postcond StackM.push_spec (value, γs, tid, stid, V').
  Proof. reflexivity. Qed.

  Local Lemma cell_add_lt ζ from to msg ζ'
      (ADD : Cell.add ζ from to msg ζ') :
    Time.lt from to.
  Proof. inversion ADD; done. Qed.

  Lemma push_simF :
    ISim.sim_fun open MA MI Ist (fid StackHdr.push).
  Proof.
    cStartFunSim. rewrite /StackI.push /StackM.push. cStepsS. cStepsT.
    destruct _q as [[[[value γs] tid] stid] V].
    iDestruct "ASM" as (stack) "[[-> ->] [#HANDLE TV]]".
    cStepsS. cStepsT.
    cStepsT.
    iApply wsim_system_yield_ir; ss.
    { apply bool_decide_true. split; last done.
      rewrite /Helping.exports elem_of_union !elem_of_singleton.
      intros [EQ|EQ]; unfold Helping.run, Helping.help in EQ; discriminate. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (st_src st_tgt) "IST TV".
    iApply wsim_system_yield_src. cStepsS.
    iApply wsim_helping_run; [simpl_map; s; f_equal|].
    iIntros (reqid) "HELP".
    rewrite SRed.bind SBRed.bind bind_bind. cNormT.
    iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt V.
    iIntros "[#HANDLE [IST [TV HELP]]] /=".
    rewrite StackI.push_loop_unfold /StackI.push_once.
    cStepsS. cStepsT. cHideS. cHideT. sYields.
    rewrite /stack_handle.
    iDestruct "HANDLE" as
      (stack_loc γstackinv γh γslot ζh_seen ζo_seen γguard ζguard γnm)
      "[%STACK [#Hinv [#SNh [#SNo #SNg]]]]".
    destruct STACK as [-> STACK_BASE].
    sYield. cStepsT.
    iEval (rewrite IstHelp_nested_equiv) in "IST".
    iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
      first by iFrame.
    iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
    iDestruct "INV" as
      (vs head offer ζh ζo Vbh Vbo Vh Vo targets nodes)
      "[Hs [HEAD [HPURE [CHAIN [SLOT [OPURE [OFFER [TARGETS REG]]]]]]]]".
    iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def) in "HEAD".
    iDestruct "HEAD" as (txh) "HEAD".
    cInlineT.
    cForceT (meta1 (tid, stid, stack_loc, Ordering.acqrel,
      ζh, ζh_seen, txh, γh, 1%Qp, CASOnly, V, Vbh))%cris.
    cForcesT. iFrame "TV SNh HEAD". iSplit; eauto.
    iSplit; ss.
    rewrite shift_0. ss.
    cStepT.
    cStepT.
    cStepT.
    iDestruct "GRT" as
      "[-> [%ζread [%fread [%na [%vret [%vactual [%Vmsg [%V1 [HREAD [#SNh1 [HEAD TV]]]]]]]]]]]".
    iDestruct "HREAD" as
      %[-> [Hval [Hseen [Hle [Hget [HVle HVmsg]]]]]].
    iPoseProof "HPURE" as "#HPUREcopy".
    iDestruct "HPUREcopy" as
      %(CURh & CASHh & PTRh & HEADH & LINKS & SENTh).
    pose proof (Hle _ _ _ Hget) as Hgeth.
    destruct (PTRh _ _ _ _ _ Hgeth) as
      (head_loc & Vguard & Hactual & Htarget & Hsafe).
    subst vactual.
    pose proof (StackHdr.le_vptr_eq Hval) as Hret. subst vret.
    simpl in HVmsg.
    iAssert (⌜current_message ζh head Vh ∧ cas_history ζh ∧
      pointer_history (stack_loc >> 2) targets ζh ∧
      head_history (stack_loc >> 2) nodes ζh ∧
      node_links (stack_loc >> 2) targets nodes ∧
      (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets)⌝)%I
      as "HPURE"; first done.
    iMod ("ACC" with "[//]") as "[ACC _]".
    iMod ("ACC" with
      "[Hs HEAD HPURE CHAIN SLOT OPURE OFFER TARGETS REG] IST") as "IST".
    { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
      iExists vs, head, offer, ζh, ζo, Vbh, Vbo, Vh, Vo, targets, nodes.
      solve_base_sl_red; iFrame "Hs HPURE CHAIN SLOT OPURE OFFER TARGETS REG".
      rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
      iExists txh. iFrame. }
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    cStepsT.
    sYield. cStepsT. cInlineT.
    cForceT (tid, stid, 3, V1). cForcesT. iFrame. iSplit; eauto.
    cStepsT.
    iDestruct "GRT" as
      "[-> [%node [%V2 [[-> %HV12] [TV [FA NODE]]]]]]".
    iEval (rewrite hist_freeable_eq /hist_freeable_def) in "FA".
    iDestruct "FA" as (alloc_tid alloc_bid) "[%NODEBASE _]".
    assert (Loc.ofs node = 0%Z) as NODE_BASE by (rewrite NODEBASE; done).
    rewrite 2!own_loc_na_vec_cons own_loc_na_vec_singleton.
    cStepsT.
    iDestruct "NODE" as "[NODE0 [NODE1 NODE2]]".
    iEval (rewrite shift_nat_assoc /=) in "NODE2".
    sYields. cStepsT. cInlineT.
    cForceT (meta0 (tid, stid, node, Val.zero, Ordering.na, V2))%cris.
    cForcesT. rewrite shift_0. iFrame "TV". iSplitL "NODE0".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    cStepsT.
    iDestruct "GRT" as "[-> [%V3 [[-> %HV23] [NODE0 TV]]]]".
    iPoseProof (view_at_cur_mon_pred V2 V3 HV23 with "NODE1") as "NODE1".
    iPoseProof (view_at_cur_mon_pred V2 V3 HV23 with "NODE2") as "NODE2".
    cStepsT.
    sYields. cStepsT. cInlineT.
    cForceT (meta0
      (tid, stid, node >> 1, Val.Vptr head_loc, Ordering.na, V3))%cris.
    cForcesT. iFrame "TV". iSplitL "NODE1".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    cStepsT.
    iDestruct "GRT" as "[-> [%V4 [[-> %HV34] [NODE1 TV]]]]".
    iPoseProof (view_at_cur_mon_pred V3 V4 HV34 with "NODE0") as "NODE0".
    iPoseProof (view_at_cur_mon_pred V3 V4 HV34 with "NODE2") as "NODE2".
    cStepsT.
    sYields. cStepsT. cInlineT.
    cForceT (meta0
      (tid, stid, node >> 2, StackHdr.encode value, Ordering.na, V4))%cris.
    cForcesT. iFrame "TV". iSplitL "NODE2".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    cStepsT.
    iDestruct "GRT" as "[-> [%V5 [[-> %HV45] [NODE2 TV]]]]".
    iPoseProof (view_at_cur_mon_pred V4 V5 HV45 with "NODE0") as "NODE0".
    iPoseProof (view_at_cur_mon_pred V4 V5 HV45 with "NODE1") as "NODE1".
    cStepsT.
    sYields. cStepsT. cInlineT.
    inversion HV12 as [Hrel12 Hcur12 Hacq12].
    inversion HV23 as [Hrel23 Hcur23 Hacq23].
    inversion HV34 as [Hrel34 Hcur34 Hacq34].
    inversion HV45 as [Hrel45 Hcur45 Hacq45].
    assert (Hcur15 : View.le (TView.cur V1) (TView.cur V5)) by
      (etrans; [exact Hcur12|]; etrans; [exact Hcur23|];
       etrans; [exact Hcur34|exact Hcur45]).
    assert (HcurV5 : View.le (TView.cur V) (TView.cur V5)) by
      (etrans; [exact HVle|exact Hcur15]).
    iPoseProof (view_at_view_mon_pred
      (view_at (AtomicSeen stack_loc γh ζread)) _ _ Hcur15
      with "SNh1") as "#SNh5".
    iPoseProof (view_at_view_mon_pred
      (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard)) _ _ HcurV5
      with "SNg") as "#SNg5".
    iEval (rewrite IstHelp_nested_equiv) in "IST".
    iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
      first by iFrame.
    iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
    iDestruct "INV" as
      (vsc headc offerc ζhc ζoc Vbhc Vboc Vhc Voc targetsc nodesc)
      "[Hsc [HEADc [HPUREc [CHAINc [SLOTc [OPUREc [OFFERc [TARGETSc REGc]]]]]]]]".
    iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def)
      in "HEADc".
    iDestruct "HEADc" as (txhc) "HEADc".
    iPoseProof (AtomicPtsToX_AtomicSeen_latest with "HEADc SNh5")
      as "%Hread_cur".
    pose proof (Hread_cur _ _ _ Hget) as Hget_cur.
    iPoseProof "HPUREc" as "#HPUREcopyc".
    iDestruct "HPUREcopyc" as
      %(CURhc & CASHhc & PTRhc & HEADHc & LINKSc & SENTc).
    destruct (PTRhc _ _ _ _ _ Hget_cur) as
      (Vhead & Vguardc & Hheadeq & Htargetc & Hsafec).
    inversion Hheadeq; subst Vhead.
    iDestruct (node_registry_fresh γnm with "NODE1 REGc") as
      "[%FRESH [NODE1 REGc]]".
    iMod (AtomicPtsTo_from_na node Val.zero with "NODE0") as
      "[%γnodeguard [%tg [%fg [%LTg [%Vg [%nag [%Vg_le [SWg PTg]]]]]]]]".
    iMod (AtomicPtsTo_from_na (node >> 1) (Val.Vptr head_loc)
      with "NODE1") as
      "[%γnext [%tn [%fn [%LTn [%Vn [%nan [%Vn_le [SWn PTn]]]]]]]]".
    set (dnew := NodeDesc head_loc value (TView.cur V5)).
    iAssert (target_record (node, TView.cur V5))%I
      with "[PTg SWg]" as "NEW_TARGET".
    { iExists fg, tg, LTg, Vg, nag, γnodeguard. iFrame. }
    iAssert (node_record node dnew)%I with "[PTn SWn]" as "NEW_NODE".
    { rewrite /node_record /immutable_field /dnew /=.
      iExists fn, tn, LTn, Vn, (TView.cur V5), nan, γnext.
      iFrame. iPureIntro. split; first done. exact Vn_le. }
    iAssert (live_value node dnew)%I with "[NODE2]" as "NEW_VALUE".
    { rewrite /live_value /dnew /=. iExists (TView.cur V5). iFrame. done. }
    assert (NODE_NE : node ≠ stack_loc >> 2) by
      (eapply base_loc_not_sentinel; eauto).
    cForceT (tid, stid, stack_loc, Val.Vptr head_loc, Val.Vptr node,
      Ordering.relaxed, Ordering.acqrel, V5, γh, ζread, Vbhc, txhc,
      ζhc, CASOnly, target_pool targetsc)%cris.
    cForcesT. rewrite shift_0.
    iFrame "TV SNh5 HEADc TARGETSc".
    change (View.le Vmsg (TView.cur V1)) in HVmsg.
    iSplit; eauto.
    { iSplitL ""; first done.
      iSplitL "".
      { iPureIntro. repeat split; eauto.
        intros t f v0 V0 b Htime Hget0.
        destruct (PTRhc _ _ _ _ _ Hget0) as
          (loc0 & Vguard0 & EQ & IN & SAFE).
        rewrite EQ. done. }
      iModIntro. iIntros "POOL". iModIntro.
      iSplit.
      { destruct Hsafec as [HSENT|Hguard].
        - subst head_loc.
          iDestruct (target_pool_lookup targetsc
            (stack_loc >> 2, Vguardc) Htargetc with "POOL") as "REC".
          iDestruct (target_record_prim with "REC") as
            (q C Vp) "PR".
          iExists q, C, Vp, γguard, ζguard. iFrame "PR SNg5".
        - assert (Hguard5 : View.le Vguardc (TView.cur V5)) by
            (etrans; [exact Hguard|]; etrans; [exact HVmsg|exact Hcur15]).
          iDestruct (target_pool_lookup targetsc
            (head_loc, Vguardc) Htargetc with "POOL") as "REC".
          iDestruct (target_record_take (head_loc, Vguardc)
            (TView.cur V5) Hguard5 with "REC") as
            (q C Vp γp Cp) "[PR #SEEN]".
          iExists q, C, Vp, γp, Cp. iFrame "PR SEEN". }
      iIntros (t f l' V' b) "%OTHER".
      destruct OTHER as (Htime & Hget' & Hne).
      destruct (PTRhc _ _ _ _ _ Hget') as
        (loc' & Vguard' & EQ & IN & SAFE).
      inversion EQ; subst loc'.
      iDestruct (target_pool_lookup targetsc (l', Vguard') IN
        with "POOL") as "REC".
      iDestruct (target_record_prim with "REC") as (q C Vp) "PR".
      iExists q, C, Vp. done. }
    cStepT. cStepT. cStepT.
    iDestruct "GRT" as "[%EQ GRT]". subst _q0.
    iDestruct "GRT" as
      (ret ζafter ζnew tcas fcas LTcas vseen Vread bcas V6)
      "[%PURE [TV [#SNh6 [TARGETSc RESULT]]]]".
    destruct PURE as
      (QRET & Hread_after & Hafter_new & Hgetcas & Htimecas & HV56).
    iAssert (⌜current_message ζhc headc Vhc ∧ cas_history ζhc ∧
      pointer_history (stack_loc >> 2) targetsc ζhc ∧
      head_history (stack_loc >> 2) nodesc ζhc ∧
      node_links (stack_loc >> 2) targetsc nodesc ∧
      (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targetsc)⌝)%I
      as "#HPUREc"; first done.
    iDestruct "RESULT" as "[FAIL|SUCCESS]".
    - iDestruct "FAIL" as "[%FAIL HEADc]".
      destruct FAIL as (-> & Hneq & HVread & Hsame). subst ζnew.
      subst _q.
      iMod ("ACC" with "[//]") as "[ACC _]".
      iMod ("ACC" with
        "[Hsc HEADc HPUREc CHAINc SLOTc OPUREc OFFERc TARGETSc REGc] IST")
        as "IST".
      { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
        iExists vsc, headc, offerc, ζhc, ζoc, Vbhc, Vboc, Vhc, Voc,
          targetsc, nodesc.
        solve_base_sl_red.
        iFrame "Hsc CHAINc SLOTc OFFERc TARGETSc REGc".
        iFrame "HPUREc OPUREc".
        rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
        iExists txhc. iFrame. }
      iEval (rewrite -IstHelp_nested_equiv) in "IST".
      cStepsT. sYields. cStepsT.
      cInlineT.
      cForceT (tid, stid, 3, V6). cForcesT. iFrame. iSplit; eauto.
      cStepsT.
      iDestruct "GRT" as
        "[-> [%offer_loc [%V7 [[-> %HV67] [TV [FA OFFER]]]]]]".
      iEval (rewrite hist_freeable_eq /hist_freeable_def) in "FA".
      iDestruct "FA" as (offer_tid offer_bid) "[%OFFERBASE _]".
      assert (Loc.ofs offer_loc = 0%Z) as OFFER_BASE by
        (rewrite OFFERBASE; done).
      rewrite 2!own_loc_na_vec_cons own_loc_na_vec_singleton.
      cStepsT. iDestruct "OFFER" as "[OFFER0 [OFFER1 OFFER2]]".
      iEval (rewrite shift_nat_assoc /=) in "OFFER2".
      sYields. cStepsT. cInlineT.
      cForceT (meta0
        (tid, stid, offer_loc, Val.zero, Ordering.na, V7))%cris.
      cForcesT. rewrite shift_0. iFrame "TV". iSplitL "OFFER0".
      { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
      cStepsT.
      iDestruct "GRT" as "[-> [%V8 [[-> %HV78] [OFFER0 TV]]]]".
      iPoseProof (view_at_cur_mon_pred V7 V8 HV78 with "OFFER1")
        as "OFFER1".
      iPoseProof (view_at_cur_mon_pred V7 V8 HV78 with "OFFER2")
        as "OFFER2".
      cStepsT. sYields. cStepsT. cInlineT.
      cForceT (meta0
        (tid, stid, offer_loc >> 1, Val.zero, Ordering.na, V8))%cris.
      cForcesT. iFrame "TV". iSplitL "OFFER1".
      { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
      cStepsT.
      iDestruct "GRT" as "[-> [%V9 [[-> %HV89] [OFFER1 TV]]]]".
      iPoseProof (view_at_cur_mon_pred V8 V9 HV89 with "OFFER0")
        as "OFFER0".
      iPoseProof (view_at_cur_mon_pred V8 V9 HV89 with "OFFER2")
        as "OFFER2".
      cStepsT. sYields. cStepsT. cInlineT.
      cForceT (meta0 (tid, stid, offer_loc >> 2,
        StackHdr.encode value, Ordering.na, V9))%cris.
      cForcesT. iFrame "TV". iSplitL "OFFER2".
      { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
      cStepsT.
      iDestruct "GRT" as "[-> [%V10 [[-> %HV910] [OFFER2 TV]]]]".
      iPoseProof (view_at_cur_mon_pred V9 V10 HV910 with "OFFER0")
        as "OFFER0".
      iPoseProof (view_at_cur_mon_pred V9 V10 HV910 with "OFFER1")
        as "OFFER1".
      cStepsT.
      inversion HV56 as [Hrel56 Hcur56 Hacq56].
      inversion HV67 as [Hrel67 Hcur67 Hacq67].
      inversion HV78 as [Hrel78 Hcur78 Hacq78].
      inversion HV89 as [Hrel89 Hcur89 Hacq89].
      inversion HV910 as [Hrel910 Hcur910 Hacq910].
      assert (HcurV10 : View.le (TView.cur V) (TView.cur V10)) by
        (etrans; [exact HcurV5|]; etrans; [exact Hcur56|];
         etrans; [exact Hcur67|]; etrans; [exact Hcur78|];
         etrans; [exact Hcur89|exact Hcur910]).
      iPoseProof (view_at_view_mon_pred
        (view_at (AtomicSeen (stack_loc >> 1) γslot ζo_seen)) _ _ HcurV10
        with "SNo") as "#SNo10".
      iPoseProof (view_at_view_mon_pred
        (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard)) _ _ HcurV10
        with "SNg") as "#SNg10".
      iMod (AtomicPtsTo_from_na offer_loc Val.zero with "OFFER0") as
        "[%γoffer_guard [%tog [%fog [%LTog [%Vog [%naog [%Vog_le [SWog PTog]]]]]]]]".
      iMod (AtomicPtsTo_from_na (offer_loc >> 1) Val.zero
        with "OFFER1") as
        "[%γstate [%tos [%fos [%LTos [%Vos [%naos [%Vos_le [SWos STATE]]]]]]]]".
      iPoseProof (AtomicSWriter_AtomicSeen with "SWog") as "#SNoffer10".
      iAssert (target_record (offer_loc, TView.cur V10))%I
        with "[PTog SWog]" as "OFFER_TARGET".
      { iExists fog, tog, LTog, Vog, naog, γoffer_guard. iFrame. }
      iPoseProof (AtomicSWriter_AtomicSeen with "SWos") as "#SNstate".
      iPoseProof (atomic_pts_to_swriter_to_cas with "STATE SWos")
        as "STATE".
      sYields. cStepsT.
      iEval (rewrite IstHelp_nested_equiv) in "IST".
      iInv "Hinv" with "[IST]" as "[IST INV]" "ACC";
        first by iFrame.
      iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INV".
      iDestruct "INV" as
        (vsd headd offerd ζhd ζod Vbhd Vbod Vhd Vod targetsd nodesd)
        "[Hsd [HEADd [HPUREd [CHAINd [SLOTd [OPUREd [OFFERd [TARGETSd REGd]]]]]]]]".
      iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def)
        in "SLOTd".
      iDestruct "SLOTd" as (txod) "SLOTd".
      iPoseProof (AtomicPtsToX_AtomicSeen_latest with "SLOTd SNo10")
        as "%Hslot_seen".
      iDestruct "HPUREd" as
        %(CURhd & CASHhd & PTRhd & HEADHd & LINKSd & SENTd).
      iDestruct "OPUREd" as %(CURod & CASHod & PTRod).
      cInlineT.
      cForceT (tid, stid, stack_loc >> 1, Val.Vptr (stack_loc >> 2),
        Val.Vptr offer_loc, Ordering.relaxed, Ordering.acqrel, V10,
        γslot, ζo_seen, Vbod, txod, ζod, CASOnly,
        target_pool ((offer_loc, TView.cur V10) :: targetsd))%cris.
      cForcesT. iFrame "TV SNo10 SLOTd".
      iFrame "OFFER_TARGET TARGETSd".
      iSplit; eauto.
      { iSplitL ""; first done.
        iSplitL "".
        { iPureIntro. repeat split; eauto.
          intros t f v0 V0 b Htime Hget0.
          destruct (PTRod _ _ _ _ _ Hget0) as
            (loc0 & Vguard0 & EQ & IN & SAFE).
          rewrite EQ. done. }
        iModIntro. iIntros "POOL". iModIntro.
        iSplit.
        { destruct SENTd as (Vsent & INsent).
          iDestruct (target_pool_lookup
            ((offer_loc, TView.cur V10) :: targetsd)
            (stack_loc >> 2, Vsent) with "POOL") as "REC".
          { right; exact INsent. }
          iDestruct (target_record_prim with "REC") as (q C Vp) "PR".
          iExists q, C, Vp, γguard, ζguard. iFrame "PR SNg10". }
        iIntros (t f l' V' b) "%OTHER".
        destruct OTHER as (Htime & Hget' & Hne).
        destruct (PTRod _ _ _ _ _ Hget') as
          (loc' & Vguard' & EQ & IN & SAFE).
        inversion EQ; subst loc'.
        iDestruct (target_pool_lookup
          ((offer_loc, TView.cur V10) :: targetsd)
          (l', Vguard') with "POOL") as "REC".
        { right; exact IN. }
        iDestruct (target_record_prim with "REC") as (q C Vp) "PR".
        iExists q, C, Vp. done. }
      cStepT. cStepT. cStepT.
      iDestruct "GRT" as "[%EQP GRT]". subst _q0.
      iDestruct "GRT" as
        (published ζpubread ζpubnew tpub fpub LTpub vpub Vpubread bpub V11)
        "[%PUBPURE [TV [#SNo11 [[OFFER_TARGET TARGETSd] PUBRESULT]]]]".
      destruct PUBPURE as
        (QPUB & Hseen_pub & Hpubread_new & Hgetpub & Htimepub & HV1011).
      inversion HV1011 as [Hrel1011 Hcur1011 Hacq1011].
      iAssert (⌜current_message ζhd headd Vhd ∧ cas_history ζhd ∧
        pointer_history (stack_loc >> 2) targetsd ζhd ∧
        head_history (stack_loc >> 2) nodesd ζhd ∧
        node_links (stack_loc >> 2) targetsd nodesd ∧
        (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targetsd)⌝)%I
        as "#HPUREd"; first done.
      iAssert (⌜current_message ζod offerd Vod ∧ cas_history ζod ∧
        pointer_history (stack_loc >> 2) targetsd ζod⌝)%I
        as "#OPUREd"; first done.
      iDestruct "PUBRESULT" as "[PUBFAIL|PUBSUCCESS]".
      { iDestruct "PUBFAIL" as "[%PUBFAIL SLOTd]".
        destruct PUBFAIL as (-> & Hpubneq & HVpubread & Hpubsame).
        subst ζpubnew. subst _q.
        iMod ("ACC" with "[//]") as "[ACC _]".
        iMod ("ACC" with
          "[Hsd HEADd HPUREd CHAINd SLOTd OPUREd OFFERd TARGETSd REGd] IST")
          as "IST".
        { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
          iExists vsd, headd, offerd, ζhd, ζod, Vbhd, Vbod, Vhd, Vod,
            targetsd, nodesd.
          solve_base_sl_red.
          iFrame "Hsd HEADd HPUREd CHAINd OPUREd OFFERd TARGETSd REGd".
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
          iExists txod. iFrame. }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        cStepsT. sYields. cStepsT.
        assert (HcurV11 : View.le (TView.cur V) (TView.cur V11)) by
          (etrans; [exact HcurV10|exact Hcur1011]).
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen stack_loc γh ζh_seen)) _ _ HcurV11
          with "SNh") as "#SNh11".
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard)) _ _ HcurV11
          with "SNg") as "#SNg11".
        iAssert (stack_handle γs (Val.Vptr stack_loc) (TView.cur V11))%I
          with "[Hinv]" as "#HANDLE11".
        { iExists stack_loc, γstackinv, γh, γslot, ζh_seen, ζpubread,
            γguard, ζguard, γnm.
          iSplit; first (iPureIntro; split; done).
          iFrame "Hinv SNh11 SNo11 SNg11". }
        unfold CS__.
        unfold cris_s.
        rewrite (push_postcond_irrel value γs tid stid V V11).
        cNormS.
        unfold CT__, cris_t. cNormT.
        cByCoind CIH. iFrame "HANDLE11 TV IST HELP WINV". }
      { iDestruct "PUBSUCCESS" as (Vpubwrite)
          "[%PUBSUCCESS [_ SLOTd]]".
        destruct PUBSUCCESS as
          (-> & Heqpub & tpubwrite & HPUBADD & Hpubvrw & Hpubvrne &
            Hpubnotle & HpubneV & Hpubord).
        subst vpub.
        subst _q.
        assert (Htpubwrite : Time.lt tpub tpubwrite) by
          (eapply cell_add_lt; exact HPUBADD).
        assert (Htpub_ne : tpub ≠ tpubwrite) by
          (intros ->; eapply Time.lt_strorder; exact Htpubwrite).
        assert (Hgetpub_base :
          Cell.get tpub ζod =
            Some (fpub, Message.message
              (Val.Vptr (stack_loc >> 2)) Vpubread bpub)).
        { pose proof (Hpubread_new _ _ _ Hgetpub) as Hgetpub_new.
          erewrite Cell.add_o in Hgetpub_new; eauto.
          destruct (Time.eq_dec tpub tpubwrite);
            [contradiction|done]. }
        assert (Hpubmax : tpub = Cell.max_ts ζod).
        { eapply cas_history_add_from_max; eauto. }
        assert (Hofferd : offerd = Val.Vptr (stack_loc >> 2)).
        { destruct CURod as (fcur & bcur & Hcur).
          rewrite <- Hpubmax in Hcur. congruence. }
        subst offerd.
        assert (HVod : Vod = Vpubread).
        { destruct CURod as (fcur & bcur & Hcur).
          rewrite <- Hpubmax in Hcur. congruence. }
        subst Vpubread.
        change (View.le (TView.cur V11) Vpubwrite) in Hpubord.
        rename Hpubord into Hcur11_pub.
        assert (CURopub : current_message ζpubnew
          (Val.Vptr offer_loc) Vpubwrite).
        { eapply current_message_add; eauto. }
        assert (CASHopub : cas_history ζpubnew).
        { eapply cas_history_add; eauto. }
        assert (PTRod' : pointer_history (stack_loc >> 2)
          ((offer_loc, TView.cur V10) :: targetsd) ζod).
        { eapply pointer_history_cons; exact PTRod. }
        assert (PTRopub : pointer_history (stack_loc >> 2)
          ((offer_loc, TView.cur V10) :: targetsd) ζpubnew).
        { eapply pointer_history_add; [exact PTRod'| |exact HPUBADD].
          exists (TView.cur V10). split; first (left; done).
          right. etrans; [exact Hcur1011|exact Hcur11_pub]. }
        assert (PTRhd' : pointer_history (stack_loc >> 2)
          ((offer_loc, TView.cur V10) :: targetsd) ζhd).
        { eapply pointer_history_cons; exact PTRhd. }
        assert (LINKSd' : node_links (stack_loc >> 2)
          ((offer_loc, TView.cur V10) :: targetsd) nodesd).
        { eapply node_links_target_cons; exact LINKSd. }
        destruct SENTd as (Vsentd & Hsentd).
        iAssert (⌜current_message ζhd headd Vhd ∧ cas_history ζhd ∧
          pointer_history (stack_loc >> 2)
            ((offer_loc, TView.cur V10) :: targetsd) ζhd ∧
          head_history (stack_loc >> 2) nodesd ζhd ∧
          node_links (stack_loc >> 2)
            ((offer_loc, TView.cur V10) :: targetsd) nodesd ∧
          (∃ Vsent, (stack_loc >> 2, Vsent) ∈
            ((offer_loc, TView.cur V10) :: targetsd))⌝)%I
          as "#HPUREpub";
          first (
            iPureIntro;
            split; [exact CURhd|];
            split; [exact CASHhd|];
            split; [exact PTRhd'|];
            split; [exact HEADHd|];
            split; [exact LINKSd'|];
            exists Vsentd; right; exact Hsentd).
        iAssert (⌜current_message ζpubnew (Val.Vptr offer_loc)
            Vpubwrite ∧
          cas_history ζpubnew ∧
          pointer_history (stack_loc >> 2)
            ((offer_loc, TView.cur V10) :: targetsd) ζpubnew⌝)%I
          as "#OPUREpub"; first done.
        assert (OFFER_NE : offer_loc ≠ stack_loc >> 2) by
          (eapply base_loc_not_sentinel; eauto).
        iMod (own_alloc (Excl ())) as "[%γoffer OfferTkn]"; first done.
        iMod (hinv_alloc
          (syn_offer_inv 0 γoffer offer_loc reqid value γs
            (TView.cur V10) (TView.cur V10))
          _ _ offerN with "[STATE OFFER2 HELP]")
          as "[%γinv #Hoinv]"; eauto.
        { solve_ndisj. }
        { solve_base_sl_red.
          iExists Val.zero,
            (Cell.singleton (Message.message Val.zero Vos naos) LTos),
            (Cell.singleton (Message.message Val.zero Vos naos) LTos),
            (TView.cur V10), Vos, γstate.
          iFrame "STATE SNstate".
          iSplit.
          { iPureIntro. repeat split.
            - done.
            - eexists fos, naos.
              rewrite Cell.max_ts_singleton Cell.singleton_get. des_ifs.
            - intros t f state Vstate b GET.
              exists 0%Z. rewrite Cell.singleton_get in GET. des_ifs.
            - intros t f state Vstate b GET.
              left. rewrite Cell.max_ts_singleton.
              rewrite Cell.singleton_get in GET. des_ifs.
            - intros t f state Vstate b GET.
              left. rewrite Cell.singleton_get in GET. des_ifs. }
          simpl. iFrame "OFFER2 HELP". }
        iAssert (is_offer 0 (stack_loc >> 2) γs
          (Val.Vptr offer_loc) Vpubwrite)%I as "#OFFERpub".
        { rewrite /is_offer.
          destruct (decide (offer_loc = stack_loc >> 2)) as [HEQ|HNE].
          - done.
          - iExists (TView.cur V10), (TView.cur V10), γinv, γoffer,
              value, reqid.
            iSplit.
            { iPureIntro. split.
              - etrans; [exact Hcur1011|exact Hcur11_pub].
              - etrans; [exact Hcur1011|exact Hcur11_pub]. }
            iExact "Hoinv". }
        iPoseProof (atomic_pts_to_seen_current
          (stack_loc >> 1) γslot txod ζpubnew ζpubread CASOnly
          (TView.cur V11) (Vbod ⊔ TView.cur V11)
          (View.join_r _ _) with "SLOTd SNo11")
          as "[SLOTd #SNopub]".
        iMod ("ACC" with "[//]") as "[ACC _]".
        iMod ("ACC" with
          "[Hsd HEADd HPUREpub CHAINd SLOTd OPUREpub OFFERpub OFFER_TARGET TARGETSd REGd] IST")
          as "IST".
        { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
          iExists vsd, headd, (Val.Vptr offer_loc), ζhd, ζpubnew,
            Vbhd, (Vbod ⊔ TView.cur V11), Vhd, Vpubwrite,
            ((offer_loc, TView.cur V10) :: targetsd), nodesd.
          solve_base_sl_red.
          iFrame "Hsd HEADd HPUREpub CHAINd OPUREpub OFFERpub REGd".
          iFrame "OFFER_TARGET TARGETSd".
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
          iExists txod. iFrame. }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        cStepsT. sYield. cStepsT. sYield. cStepsT.
        iPoseProof (view_at_view_mon_pred
          (view_at (AtomicSeen offer_loc γoffer_guard
            (Cell.singleton (Message.message Val.zero Vog naog) LTog)))
          _ _ Hcur1011 with "SNoffer10") as "#SNoffer11".
        iEval (rewrite IstHelp_nested_equiv) in "IST".
        iInv "Hinv" with "[IST]" as "[IST INVe]" "ACCe";
          first by iFrame.
        iEval (rewrite stack_inv'_eq; solve_base_sl_red) in "INVe".
        iDestruct "INVe" as
          (vse heade offere ζhe ζoe Vbhe Vboe Vhe Voe targetse nodese)
          "[Hse [HEADe [HPUREe [CHAINe [SLOTe [OPUREe [OFFERe [TARGETSe REGe]]]]]]]]".
        iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def)
          in "SLOTe".
        iDestruct "SLOTe" as (txoe) "SLOTe".
        iPoseProof (AtomicPtsToX_AtomicSeen_latest with "SLOTe SNopub")
          as "%Hpub_cur".
        destruct (Cell.add_get0 HPUBADD) as [_ Hgetpubwrite].
        pose proof (Hpub_cur _ _ _ Hgetpubwrite) as Hgetpubwrite_e.
        iPoseProof "HPUREe" as "#HPUREcopye".
        iDestruct "HPUREcopye" as
          %(CURhe & CASHhe & PTRhe & HEADHe & LINKSe & SENTe).
        iPoseProof "OPUREe" as "#OPUREcopye".
        iDestruct "OPUREcopye" as %(CURoe & CASHoe & PTRoe).
        destruct (PTRoe _ _ _ _ _ Hgetpubwrite_e) as
          (offer_e & Voguarde & EQoffer & Htargete & Hsafee).
        inversion EQoffer; subst offer_e.
        cInlineT.
        cForceT (tid, stid, stack_loc >> 1, Val.Vptr offer_loc,
          Val.Vptr (stack_loc >> 2), Ordering.relaxed, Ordering.acqrel,
          V11, γslot, ζpubread, Vboe, txoe, ζoe, CASOnly,
          target_pool targetse)%cris.
        cForcesT.
        iSplitL "TV SLOTe TARGETSe".
        { iSplit.
          { iPureIntro. reflexivity. }
          iFrame "TV SNo11 SLOTe TARGETSe".
          iSplit.
          { iPureIntro. repeat split; eauto.
            intros t f value0 V0 b Htime Hget0.
            destruct (PTRoe _ _ _ _ _ Hget0) as
              (loc0 & Vguard0 & EQ & IN & SAFE).
            subst value0. done. }
          iModIntro. iIntros "TARGETSe". iModIntro. iSplit.
          { iDestruct (target_pool_lookup _ _ Htargete with "TARGETSe")
              as "REC".
            iDestruct (target_record_prim with "REC") as (q C Vp) "PRIM".
            iExists q, C, Vp, γoffer_guard,
              (Cell.singleton (Message.message Val.zero Vog naog) LTog).
            iFrame "PRIM SNoffer11". }
          iIntros (t f loc V0 b) "%OTHER".
          destruct OTHER as (_ & GET & NE).
          destruct (PTRoe _ _ _ _ _ GET) as
            (loc2 & Vg2 & EQ & IN & SAFE). inversion EQ; subst loc2.
          iDestruct (target_pool_lookup _ _ IN with "TARGETSe") as "REC".
          iDestruct (target_record_prim with "REC") as (q C Vp) "PRIM".
          iExists q, C, Vp. done. }
        cStepT. cStepT. cStepT.
        iDestruct "GRT" as
          "[-> [%cleared [%ζclearread [%ζclearnew [%tclear [%fclear [%LTclear [%vclear [%Vclearread [%bclear [%V12 [HCLEAR [TV [#SNo12 [TARGETSe HCLEARCASE]]]]]]]]]]]]]]]".
        iDestruct "HCLEAR" as
          %[-> [Hseen1112 [Hclearread_new
            [Hgetclear [Htimeclear HV1112]]]]].
        iDestruct "HCLEARCASE" as "[CLEARFAIL|CLEARSUCC]".
        { iDestruct "CLEARFAIL" as "[%CLEARFAIL SLOTe]".
          destruct CLEARFAIL as (-> & Hclearneq & Hclearacq & ->).
          iAssert (⌜current_message ζhe heade Vhe ∧ cas_history ζhe ∧
            pointer_history (stack_loc >> 2) targetse ζhe ∧
            head_history (stack_loc >> 2) nodese ζhe ∧
            node_links (stack_loc >> 2) targetse nodese ∧
            (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targetse)⌝)%I
            as "#HPUREe"; first done.
          iAssert (⌜current_message ζclearnew offere Voe ∧
            cas_history ζclearnew ∧
            pointer_history (stack_loc >> 2) targetse ζclearnew⌝)%I
            as "#OPUREe"; first done.
          iMod ("ACCe" with "[//]") as "[ACCe _]".
          iMod ("ACCe" with
            "[Hse HEADe HPUREe CHAINe SLOTe OPUREe OFFERe TARGETSe REGe] IST")
            as "IST".
          { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
            iExists vse, heade, offere, ζhe, ζclearnew, Vbhe, Vboe,
              Vhe, Voe, targetse, nodese.
            solve_base_sl_red.
            iFrame "Hse HEADe HPUREe CHAINe OPUREe OFFERe TARGETSe REGe".
            rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
            iExists txoe. iFrame. }
          iEval (rewrite -IstHelp_nested_equiv) in "IST".
          shelve. }
        { iDestruct "CLEARSUCC" as (Vclearwrite)
            "[%CLEARSUCC [_ SLOTe]]".
          destruct CLEARSUCC as
            (-> & Heqclear & tclearwrite & HCLEARADD & Hclearvrw &
              Hclearvrne & Hclearnotle & HclearneV & Hclearord).
          subst vclear.
          assert (Htclearwrite : Time.lt tclear tclearwrite) by
            (eapply cell_add_lt; exact HCLEARADD).
          assert (Htclear_ne : tclear ≠ tclearwrite) by
            (intros ->; eapply Time.lt_strorder; exact Htclearwrite).
          assert (Hgetclear_base :
            Cell.get tclear ζoe =
              Some (fclear, Message.message
                (Val.Vptr offer_loc) Vclearread bclear)).
          { pose proof (Hclearread_new _ _ _ Hgetclear) as Hgetclear_new.
            erewrite Cell.add_o in Hgetclear_new; eauto.
            destruct (Time.eq_dec tclear tclearwrite);
              [contradiction|done]. }
          assert (Hclearmax : tclear = Cell.max_ts ζoe).
          { eapply cas_history_add_from_max; eauto. }
          assert (Hoffere : offere = Val.Vptr offer_loc).
          { destruct CURoe as (fcur & bcur & Hcur).
            rewrite <- Hclearmax in Hcur. congruence. }
          subst offere.
          assert (HVoe : Voe = Vclearread).
          { destruct CURoe as (fcur & bcur & Hcur).
            rewrite <- Hclearmax in Hcur. congruence. }
          subst Vclearread.
          change (View.le (TView.cur V12) Vclearwrite) in Hclearord.
          rename Hclearord into Hcur12_clear.
          assert (CURoclear : current_message ζclearnew
            (Val.Vptr (stack_loc >> 2)) Vclearwrite).
          { eapply current_message_add; eauto. }
          assert (CASHoclear : cas_history ζclearnew).
          { eapply cas_history_add; eauto. }
          destruct SENTe as (Vsente & Hsente).
          assert (PTRoclear : pointer_history (stack_loc >> 2)
            targetse ζclearnew).
          { eapply pointer_history_add; [exact PTRoe| |exact HCLEARADD].
            exists Vsente. split; first exact Hsente. left; done. }
          iAssert (⌜current_message ζhe heade Vhe ∧ cas_history ζhe ∧
            pointer_history (stack_loc >> 2) targetse ζhe ∧
            head_history (stack_loc >> 2) nodese ζhe ∧
            node_links (stack_loc >> 2) targetse nodese ∧
            (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targetse)⌝)%I
            as "#HPUREe".
          { iPureIntro.
            split; [exact CURhe|].
            split; [exact CASHhe|].
            split; [exact PTRhe|].
            split; [exact HEADHe|].
            split; [exact LINKSe|].
            exists Vsente. exact Hsente. }
          iAssert (⌜current_message ζclearnew
              (Val.Vptr (stack_loc >> 2)) Vclearwrite ∧
            cas_history ζclearnew ∧
            pointer_history (stack_loc >> 2) targetse ζclearnew⌝)%I
            as "#OPUREclear"; first done.
          iAssert (is_offer 0 (stack_loc >> 2) γs
            (Val.Vptr (stack_loc >> 2)) Vclearwrite)%I
            as "#OFFERclear".
          { rewrite /is_offer.
            destruct (decide (stack_loc >> 2 = stack_loc >> 2))
              as [HEQ|HNE].
            - done.
            - exfalso. apply HNE. reflexivity. }
          iMod ("ACCe" with "[//]") as "[ACCe _]".
          iMod ("ACCe" with
            "[Hse HEADe HPUREe CHAINe SLOTe OPUREclear OFFERclear TARGETSe REGe] IST")
            as "IST".
          { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
            iExists vse, heade, (Val.Vptr (stack_loc >> 2)), ζhe,
              ζclearnew, Vbhe, (Vboe ⊔ TView.cur V12), Vhe,
              Vclearwrite, targetse, nodese.
            solve_base_sl_red.
            iFrame "Hse HEADe HPUREe CHAINe OPUREclear OFFERclear TARGETSe REGe".
            rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
            iExists txoe. iFrame. }
          iEval (rewrite -IstHelp_nested_equiv) in "IST".
          shelve. }
        Unshelve.
        all: sYield; cStepsT; sYield; cStepsT;
          iEval (rewrite IstHelp_nested_equiv) in "IST";
          iInv "Hoinv" with "[IST]" as "[IST OINV]" "OACC".
        all: try (by iFrame).
        all: iEval (solve_base_sl_red) in "OINV";
          iDestruct "OINV" as
            (state ζstate ζstate_seen Vbstate Vmsgstate γstate')
            "[STATE [#SNstate' [STATEPURE OSTATE]]]";
          iDestruct "STATEPURE" as
            %(Hstate_seen & CURstate & NUMstate & CASHstate & STATEHIST);
          inversion HV1112 as [Hrel1112 Hcur1112 Hacq1112];
          assert (Hcur1012 : View.le (TView.cur V10) (TView.cur V12)) by
            (etrans; [exact Hcur1011|exact Hcur1112]);
          iPoseProof (view_at_view_mon_pred
            (view_at (AtomicSeen (offer_loc >> 1) γstate' ζstate_seen))
            _ _ Hcur1012 with "SNstate'") as "#SNstate12";
          iEval (rewrite AtomicPtsTo_eq /AtomicPtsTo_def) in "STATE";
          iDestruct "STATE" as (txstate) "STATE";
          cInlineT;
          cForceT (tid, stid, offer_loc >> 1, Val.zero, Val.Vnum 2,
            Ordering.acqrel, Ordering.acqrel, V12, γstate', ζstate_seen,
            Vbstate, txstate, ζstate, CASOnly, emp%I)%cris;
          cForcesT;
          iSplitL "TV STATE".
        all: try (
          iSplit;
          [ iPureIntro; repeat split; eauto
          | iFrame "TV SNstate12 STATE";
            iSplit;
            [ iPureIntro; repeat split; eauto;
              intros t f v V0 b _ Hget0;
              destruct (NUMstate _ _ _ _ _ Hget0) as [z ->]; done
            | solve_base_sl_red ] ]).
        all: cStepsT;
          iDestruct "GRT" as
            "[-> [%withdrew [%ζstate_read [%ζstate_new [%tstate [%fstate [%LTstate [%vstate [%Vstate_read [%bstate [%V13 [HWITHDRAW [TV [#SNstate13 [_ HWITHDRAWCASE]]]]]]]]]]]]]]]";
          iDestruct "HWITHDRAW" as
            %[-> [Hstate_seen1213 [Hstate_read_new
              [Hstate_get [Htstate HV1213]]]]];
          iDestruct "HWITHDRAWCASE" as "[WITHDRAWFAIL|WITHDRAWSUCC]".
        2: shelve.
        3: shelve.
        all: (
          iDestruct "WITHDRAWFAIL" as "[%WITHDRAWFAIL STATE]";
          destruct WITHDRAWFAIL as
            (-> & Hwithdrawneq & Hwithdrawacq & ->);
          pose proof (Hstate_read_new _ _ _ Hstate_get)
            as Hstate_get_full;
          destruct (STATEHIST _ _ _ _ _ Hstate_get_full)
            as [Hstate_zero|Hstate_current];
          [ subst vstate; contradiction
          | subst vstate;
            destruct (NUMstate _ _ _ _ _ Hstate_get_full)
              as (z & Hstate_num);
            subst state;
            iEval (simpl) in "OSTATE";
            destruct_decide (decide (z = 0%Z)) as Hz0;
            [ subst z; contradiction
            | destruct_decide (decide (z = 1%Z)) as Hz1;
              [ subst z;
                iPoseProof "OSTATE" as "#Done";
                iAssert (@{Vbstate} (offer_loc >> 1) cas↦{γstate'}
                  ζstate_new)%I with "[STATE]" as "STATE";
                [ rewrite AtomicPtsTo_eq /AtomicPtsTo_def;
                  iExists txstate; done
                |];
                iMod ("OACC" with "[//]") as "[OACC _]";
                iMod ("OACC" with "[STATE Done] IST") as "IST";
                [ solve_base_sl_red;
                  iExists Val.one, ζstate_new, ζstate_seen,
                    Vbstate, Vmsgstate, γstate';
                  iFrame "STATE SNstate' Done"; done
                |];
                iEval (rewrite -IstHelp_nested_equiv) in "IST";
                cStepsT; sYield; cStepsT;
                sYieldS;
                iApply (wsim_HelpDone_try_run with "Done");
                cStepsS; sYieldS; cStepsS; cForcesS;
                iSplitL "TV";
                [ iSplit;
                  [ done
                  | iExists V13; iSplit; [done|iFrame "TV"] ]
                |];
                cStepsS; cStepsT; cStep; iFrame "IST"; done
              | destruct_decide (decide (z = 2%Z)) as Hz2;
                [ subst z; iCombine "OfferTkn OSTATE" gives %WF; done
                | done ]
              ]
            ]
          ]).
        Unshelve.
        all: (
          iDestruct "WITHDRAWSUCC" as (Vstate_write)
            "[%WITHDRAWSUCC [_ STATE]]";
          destruct WITHDRAWSUCC as
            (-> & Heqwithdraw & tstate_write & HSTATEADD & Hstatevrw &
              Hstatevrne & Hstatenotle & HstateneV & Hstateord);
          subst vstate;
          assert (Htstate_write : Time.lt tstate tstate_write) by
            (eapply cell_add_lt; exact HSTATEADD);
          assert (Htstate_ne : tstate ≠ tstate_write) by
            (intros ->; eapply Time.lt_strorder; exact Htstate_write);
          assert (Hstate_get_base :
            Cell.get tstate ζstate =
              Some (fstate,
                Message.message Val.zero Vstate_read bstate)) by
            (pose proof (Hstate_read_new _ _ _ Hstate_get) as Hget_new;
             erewrite Cell.add_o in Hget_new; eauto;
             destruct (Time.eq_dec tstate tstate_write);
               [contradiction|done]);
          assert (Hstatemax : tstate = Cell.max_ts ζstate) by
            (eapply cas_history_add_from_max; eauto);
          assert (Hstatezero : state = Val.zero) by
            (destruct CURstate as (fcur & bcur & Hcur);
             rewrite <- Hstatemax in Hcur; congruence);
          subst state;
          iEval (simpl) in "OSTATE";
          iDestruct "OSTATE" as "[PAYLOAD HELP]";
          change (Vstate_write = TView.cur V13) in Hstateord;
          subst Vstate_write;
          assert (CURstate_new : current_message ζstate_new
            (Val.Vnum 2) (TView.cur V13)) by
            (eapply current_message_add; eauto);
          assert (NUMstate_new : numeric_history ζstate_new) by
            (eapply numeric_history_add; eauto);
          assert (CASHstate_new : cas_history ζstate_new) by
            (eapply cas_history_add; eauto);
          assert (STATEHISTnew :
            offer_state_history ζstate_new (Val.Vnum 2)) by
            (eapply offer_state_history_add_from_zero; eauto);
          assert (Hstate_seen_new : Cell.le ζstate_seen ζstate_new) by
            (etrans; eauto);
          iAssert (@{Vbstate ⊔ TView.cur V13}
            (offer_loc >> 1) cas↦{γstate'} ζstate_new)%I
            with "[STATE]" as "STATE";
          [ rewrite AtomicPtsTo_eq /AtomicPtsTo_def;
            iExists txstate; done
          |];
          iMod ("OACC" with "[//]") as "[OACC _]";
          iMod ("OACC" with "[STATE OfferTkn] IST") as "IST";
          [ solve_base_sl_red;
            iExists (Val.Vnum 2), ζstate_new, ζstate_seen,
              (Vbstate ⊔ TView.cur V13), (TView.cur V13), γstate';
            iFrame "STATE SNstate'";
            iSplit;
            [ done
            | simpl; repeat case_decide; try lia; iFrame "OfferTkn" ]
          |];
          iEval (rewrite -IstHelp_nested_equiv) in "IST";
          cStepsT; sYield; cStepsT;
          inversion HV1213 as [Hrel1213 Hcur1213 Hacq1213];
          assert (HcurV13 : View.le (TView.cur V) (TView.cur V13)) by
            (etrans; [exact HcurV10|]; etrans; [exact Hcur1011|];
              etrans; [exact Hcur1112|exact Hcur1213]);
          iPoseProof (view_at_view_mon_pred
            (view_at (AtomicSeen stack_loc γh ζh_seen)) _ _ HcurV13
            with "SNh") as "#SNh13";
          iPoseProof (view_at_view_mon_pred
            (view_at (AtomicSeen (stack_loc >> 1) γslot ζclearread))
            _ _ Hcur1213 with "SNo12") as "#SNo13";
          iPoseProof (view_at_view_mon_pred
            (view_at (AtomicSeen (stack_loc >> 2) γguard ζguard))
            _ _ HcurV13 with "SNg") as "#SNg13";
          iAssert (stack_handle γs (Val.Vptr stack_loc) (TView.cur V13))%I
            with "[]" as "#HANDLE13";
          [ rewrite /stack_handle;
            iExists stack_loc, γstackinv, γh, γslot, ζh_seen, ζclearread,
              γguard, ζguard, γnm;
            iSplit; [done|iFrame "Hinv SNh13 SNo13 SNg13"]
          |];
          unfold CS__, cris_s;
          rewrite (push_postcond_irrel value γs tid stid V V13);
          cNormS;
          unfold CT__, cris_t; cNormT;
          cByCoind CIH; iFrame "HANDLE13 TV IST HELP WINV").
      }
    - iDestruct "SUCCESS" as (Vw) "[%SUCC [_ HEADc]]".
      clear CIH.
      destruct SUCC as
        (-> & Heq & twrite & HADD & Hvrw & Hvrne &
          Hnotle & HneqV & Hord).
      subst vseen.
      assert (Htwrite : Time.lt tcas twrite) by
        (eapply cell_add_lt; exact HADD).
      assert (Htcas_ne : tcas ≠ twrite) by
        (intros ->; eapply Time.lt_strorder; exact Htwrite).
      assert (Hget_base :
        Cell.get tcas ζhc =
          Some (fcas, Message.message (Val.Vptr head_loc) Vread bcas)).
      { pose proof (Hafter_new _ _ _ Hgetcas) as Hget_new.
        erewrite Cell.add_o in Hget_new; eauto.
        destruct (Time.eq_dec tcas twrite); [contradiction|done]. }
      assert (Hmax : tcas = Cell.max_ts ζhc).
      { eapply cas_history_add_from_max; eauto. }
      pose proof CURhc as CURhc0.
      assert (Hheadc : headc = Val.Vptr head_loc).
      { destruct CURhc0 as (fcur & bcur & Hcur).
        rewrite <- Hmax in Hcur. congruence. }
      subst headc.
      inversion HV56 as [Hrel56 Hcur56 Hacq56].
      change (View.le (TView.cur V6) Vw) in Hord.
      assert (Hpubw : View.le (TView.cur V5) Vw) by
        (etrans; [exact Hcur56|exact Hord]).
      assert (Hmsg5 : View.le Vmsg (TView.cur V5)) by
        (etrans; [exact HVmsg|exact Hcur15]).
      assert (NEWLINK :
        dnew.(node_next) = stack_loc >> 2 ∨
          ∃ dnext Vnext,
            nodesc !! dnew.(node_next) = Some dnext ∧
            (dnew.(node_next), Vnext) ∈ targetsc ∧
            View.le dnext.(node_pub_view) dnew.(node_pub_view) ∧
            View.le Vnext dnew.(node_pub_view)).
      { rewrite /dnew /=.
        destruct (decide (head_loc = stack_loc >> 2))
          as [->|Hnext_ne]; first by left.
        right.
        destruct (head_history_lookup _ _ _ _ _ _ _ _
          Hnext_ne Hget_cur HEADHc) as (dnext & LOOKnext & LEpubnext).
        destruct Hsafec as [HSENT|LEguard]; first contradiction.
        exists dnext, Vguardc.
        split; [exact LOOKnext|].
        split; [exact Htargetc|].
        split.
        - etrans; [exact LEpubnext|exact Hmsg5].
        - etrans; [exact LEguard|exact Hmsg5]. }
      assert (CURhnew : current_message ζnew (Val.Vptr node) Vw).
      { eapply current_message_add; eauto. }
      assert (CASHhnew : cas_history ζnew).
      { eapply cas_history_add; eauto. }
      assert (PTRhc' : pointer_history (stack_loc >> 2)
        ((node, TView.cur V5) :: targetsc) ζhc).
      { eapply pointer_history_cons; exact PTRhc. }
      assert (PTRhnew : pointer_history (stack_loc >> 2)
        ((node, TView.cur V5) :: targetsc) ζnew).
      { eapply pointer_history_add; [exact PTRhc'| |exact HADD].
        exists (TView.cur V5). split; first (left; done).
        right. exact Hpubw. }
      assert (HEADHc' : head_history (stack_loc >> 2)
        (<[node := dnew]> nodesc) ζhc).
      { eapply head_history_insert; eauto. }
      assert (HEADHnew : head_history (stack_loc >> 2)
        (<[node := dnew]> nodesc) ζnew).
      { eapply head_history_add; [exact HEADHc'| |exact HADD].
        right. exists dnew. split; first by rewrite lookup_insert.
        rewrite /dnew /=. exact Hpubw. }
      assert (LINKSnew : node_links (stack_loc >> 2)
        ((node, TView.cur V5) :: targetsc)
        (<[node := dnew]> nodesc)).
      { eapply (node_links_insert (stack_loc >> 2) targetsc nodesc
          node dnew (TView.cur V5)); eauto. }
      iDestruct "OPUREc" as %(CURoc & CASHoc & PTRoc).
      assert (PTRoc' : pointer_history (stack_loc >> 2)
        ((node, TView.cur V5) :: targetsc) ζoc).
      { eapply pointer_history_cons; exact PTRoc. }
      destruct SENTc as (Vsentc & Hsentc).
      iAssert (⌜current_message ζnew (Val.Vptr node) Vw ∧
        cas_history ζnew ∧
        pointer_history (stack_loc >> 2)
          ((node, TView.cur V5) :: targetsc) ζnew ∧
        head_history (stack_loc >> 2)
          (<[node := dnew]> nodesc) ζnew ∧
        node_links (stack_loc >> 2)
          ((node, TView.cur V5) :: targetsc)
          (<[node := dnew]> nodesc) ∧
        (∃ Vsent, (stack_loc >> 2, Vsent) ∈
          ((node, TView.cur V5) :: targetsc))⌝)%I
        as "#HPUREnew".
      { iPureIntro.
        split; [exact CURhnew|].
        split; [exact CASHhnew|].
        split; [exact PTRhnew|].
        split; [exact HEADHnew|].
        split; [exact LINKSnew|].
        exists Vsentc. right. exact Hsentc. }
      iAssert (⌜current_message ζoc offerc Voc ∧
        cas_history ζoc ∧
        pointer_history (stack_loc >> 2)
          ((node, TView.cur V5) :: targetsc) ζoc⌝)%I
        as "#OPUREnew"; first done.
      iPoseProof (live_chain_insert_mono
        (stack_loc >> 2) nodesc vsc (Val.Vptr head_loc) node dnew FRESH
        with "CHAINc") as "CHAINoldnew".
      iAssert (live_chain (stack_loc >> 2)
        (<[node := dnew]> nodesc) (value :: vsc) (Val.Vptr node))%I
        with "[NEW_VALUE CHAINoldnew]" as "CHAINnew".
      { simpl. iExists node, dnew. rewrite /dnew /=.
        iSplit.
        { iPureIntro. repeat split; eauto. by rewrite lookup_insert. }
        iFrame. }
      iMod (node_registry_insert γnm nodesc node dnew FRESH
        with "NEW_NODE REGc") as "REGc".
      iMod ("ACC" with "[//]") as "[_ > ACC]".
      sYieldS. prependRetT tt.
      iApply (wsim_helping_pend_try_run with "HELP [-]").
      aUnfoldS. rewrite /StackM.jobCode.
      cNormS. sYieldS. cStepsS.
      iDestruct (stack_content_auth_agree with "Hsc ASM") as %Hstack.
      subst _q.
      subst _q0.
      iMod (stack_content_auth_update γs vsc (value :: vsc)
        with "Hsc ASM") as "[Hsc ASM]".
      cForcesS; first iFrame "ASM".
      cStep.
      iFrame "WINV".
      iIntros "#Done".
      cStepsS.
      iMod ("ACC" with
        "[Hsc HEADc HPUREnew CHAINnew SLOTc OPUREnew OFFERc NEW_TARGET TARGETSc REGc] IST")
        as "IST".
      { iEval (rewrite stack_inv'_eq; solve_base_sl_red).
        iExists (value :: vsc), (Val.Vptr node), offerc,
          ζnew, ζoc, (Vbhc ⊔ TView.cur V6), Vboc, Vw, Voc,
          ((node, TView.cur V5) :: targetsc), (<[node := dnew]> nodesc).
        solve_base_sl_red.
        iFrame "Hsc HPUREnew CHAINnew SLOTc OPUREnew OFFERc REGc".
        iFrame "NEW_TARGET TARGETSc".
        rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def.
        iExists txhc. iFrame. }
      iEval (rewrite -IstHelp_nested_equiv) in "IST".
      cStepsT. sYield. cStepsT.
      sYieldS. cStepsS. cForcesS.
      iSplitL "TV".
      { iSplit; first done.
        iExists V6. iSplit; first done. iFrame "TV". }
      cStepsS. cStepsT. cStep. iFrame "IST". done.
  Qed.
End StackIM.
