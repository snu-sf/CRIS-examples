Require Import CRIS.common.CRIS.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.system Require Import SystemHeader SystemA SystemTactics.
From CRIS.promise_free.elimination_stack Require Import StackHeader StackA StackI.
From CRIS.helping Require Import HelpingTactics.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG,
    _SYS: !sysGS, _STACK: !stackG, _HELP: !helpingGS, !schGS}.
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
  Local Definition Ist :=
    IstProd (IstSB [mn] (IstHelp IstTrue ⊤)) IstEq.

  Lemma new_stack_simF :
    ISim.sim_fun open MA MI Ist (fid StackHdr.new_stack).
  Proof.
    cStartFunSim. rewrite /StackI.new_stack /StackM.new_stack.
    cStepsS. destruct _q as [[tid stid] V].
    iDestruct "ASM" as "[-> [-> TV]]".
    rewrite /StackI.new_stack /StackM.new_stack. cStepsS.
    cStepsT. cInlineT.
    cForceT (tid, stid, 3, V). cForcesT. iFrame. iSplit; eauto.
    cStepsT. iDestruct "GRT" as "[-> [%loc [%V' [[-> %LE] [TV [FA ↦]]]]]]".
    iEval (rewrite hist_freeable_eq /hist_freeable_def) in "FA".
    iDestruct "FA" as (alloc_tid alloc_bid) "[%LOCBASE _]".
    assert (Loc.ofs loc = 0%Z) as BASE by (rewrite LOCBASE; done).
    rewrite 2!own_loc_na_vec_cons own_loc_na_vec_singleton.
    cStepsT.
    iApply wsim_system_yield_ir; ss.
    { apply bool_decide_true. split; last done.
      rewrite /Helping.exports elem_of_union !elem_of_singleton.
      intros [EQ|EQ]; unfold Helping.run, Helping.help in EQ; discriminate. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    cStepsT.

    iApply wsim_system_yield_ir; ss.
    { apply bool_decide_true. split; last done.
      rewrite /Helping.exports elem_of_union !elem_of_singleton.
      intros [EQ|EQ]; unfold Helping.run, Helping.help in EQ; discriminate. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".

    cStepsT. cInlineT.
    cForceT (meta0 (tid, stid, loc >> 2, Val.zero, Ordering.na, _))%cris.
    cForcesT. iFrame "TV".
    iDestruct "↦" as "[↦head [↦offer ↦guard]]".
    iEval (rewrite shift_nat_assoc /=) in "↦guard". iSplitL "↦guard".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    cStepsT. iDestruct "GRT" as "[-> [%V'' [[-> %LE'] [↦guard TV]]]]".
    iPoseProof (view_at_cur_mon_pred V' V'' LE' with "↦head") as "↦head".
    iPoseProof (view_at_cur_mon_pred V' V'' LE' with "↦offer") as "↦offer".
    cStepsT.

    iApply wsim_system_yield_ir; ss.
    { apply bool_decide_true. split; last done.
      rewrite /Helping.exports elem_of_union !elem_of_singleton.
      intros [EQ|EQ]; unfold Helping.run, Helping.help in EQ; discriminate. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".

    cStepsT. cInlineT.
    cForceT (meta0
      (tid, stid, loc, Val.Vptr (loc >> 2), Ordering.na, _))%cris.
    cForcesT. rewrite shift_0. iFrame "TV". iSplitL "↦head".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    cStepsT. iDestruct "GRT" as "[-> [%V3 [[-> %LE3] [↦head TV]]]]".
    iPoseProof (view_at_cur_mon_pred V'' V3 LE3 with "↦offer") as "↦offer".
    iPoseProof (view_at_cur_mon_pred V'' V3 LE3 with "↦guard") as "↦guard".
    cStepsT.

    iApply wsim_system_yield_ir; ss.
    { apply bool_decide_true. split; last done.
      rewrite /Helping.exports elem_of_union !elem_of_singleton.
      intros [EQ|EQ]; unfold Helping.run, Helping.help in EQ; discriminate. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    cStepsT. cInlineT.
    cForceT (meta0
      (tid, stid, loc >> 1, Val.Vptr (loc >> 2), Ordering.na, _))%cris.
    cForcesT. iFrame "TV". iSplitL "↦offer".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    cStepsT. iDestruct "GRT" as "[-> [%V4 [[-> %LE4] [↦offer TV]]]]".
    cStepsT.

    iApply wsim_system_yield_ir; ss.
    { apply bool_decide_true. split; last done.
      rewrite /Helping.exports elem_of_union !elem_of_singleton.
      intros [EQ|EQ]; unfold Helping.run, Helping.help in EQ; discriminate. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV". cStepsT.

    iPoseProof (view_at_cur_mon_pred V3 V4 LE4 with "↦head") as "↦head".
    iPoseProof (view_at_cur_mon_pred V3 V4 LE4 with "↦guard") as "↦guard".
    iMod (AtomicPtsTo_from_na loc (Val.Vptr (loc >> 2)) with "↦head")
      as "[%γh [%th [%fh [%LTh [%Vh [%nah [%Vh_le [SWh ↦head]]]]]]]]".
    iMod (AtomicPtsTo_from_na (loc >> 1) (Val.Vptr (loc >> 2)) with "↦offer")
      as "[%γslot [%to [%fo [%LTo [%Vo [%nao [%Vo_le [SWo ↦offer]]]]]]]]".
    iMod (AtomicPtsTo_from_na (loc >> 2) Val.zero with "↦guard")
      as "[%γguard [%tg [%fg [%LTg [%Vg [%nag [%Vg_le [SWg ↦guard]]]]]]]]".
    iPoseProof (AtomicSWriter_AtomicSeen with "SWh") as "#SNh".
    iPoseProof (AtomicSWriter_AtomicSeen with "SWo") as "#SNo".
    iPoseProof (AtomicSWriter_AtomicSeen with "SWg") as "#SNg".
    iPoseProof (atomic_pts_to_swriter_to_cas with "↦head SWh") as "↦head".
    iPoseProof (atomic_pts_to_swriter_to_cas with "↦offer SWo") as "↦offer".
    iMod (own_alloc (● Excl' ([] : list stackValO) ⋅ ◯ Excl' []))
      as "[%γs [Hs● Hs◯]]".
    { apply auth_both_valid_discrete; split; done. }
    iMod node_registry_alloc as "[%γnm REG]".

    iMod (hinv_alloc (stack_inv' 0 γs loc γh γslot γnm) _ _ stackInvN
      with "[Hs● ↦head ↦offer ↦guard SWg REG]") as "[%γinv #Hinv]"; eauto.
    { solve_ndisj. }
    { rewrite stack_inv'_eq. solve_base_sl_red.
      iExists [], (Val.Vptr (loc >> 2)), (Val.Vptr (loc >> 2)),
        (Cell.singleton (Message.message (Val.Vptr (loc >> 2)) Vh nah) LTh),
        (Cell.singleton (Message.message (Val.Vptr (loc >> 2)) Vo nao) LTo),
        (TView.cur V4), (TView.cur V4), Vh, Vo,
        [(loc >> 2, TView.cur V4)], (∅ : gmap Loc.t node_desc).
      solve_base_sl_red; iFrame.
      iSplitL "↦head"; first (rewrite syn_AtomicPtsTo_red; iFrame).
      iSplit.
      { iPureIntro.
        split.
        - eexists fh, nah.
          rewrite Cell.max_ts_singleton Cell.singleton_get. des_ifs.
        - split.
          + intros t f v Vmsg b GET.
            left. rewrite Cell.max_ts_singleton.
            rewrite Cell.singleton_get in GET. des_ifs.
          + split.
            * intros t f v Vmsg b GET.
              exists (loc >> 2), (TView.cur V4).
              rewrite Cell.singleton_get in GET. des_ifs.
              split; first done. split; first (left; done). left; done.
            * split.
              { intros t f v Vmsg b GET.
                left. rewrite Cell.singleton_get in GET. des_ifs. }
              { split.
                - intros node0 d0 LOOK.
                  rewrite lookup_empty in LOOK. congruence.
                - exists (TView.cur V4). left; done. }
      }
      iSplit; first done.
      iSplitL "↦offer"; first (rewrite syn_AtomicPtsTo_red; iFrame).
      iSplit.
      { iPureIntro. repeat split.
        - eexists fo, nao.
          rewrite Cell.max_ts_singleton Cell.singleton_get. des_ifs.
        - intros t f v Vmsg b GET.
          left. rewrite Cell.max_ts_singleton.
          rewrite Cell.singleton_get in GET. des_ifs.
        - intros t f v Vmsg b GET.
          exists (loc >> 2), (TView.cur V4).
          rewrite Cell.singleton_get in GET. des_ifs.
          split; first done. split; first (left; done). left; done.
      }
      case_decide; [done|contradiction]. }
    iApply wsim_system_yield_src.
    sYieldS.
    cForceS (Val.Vptr loc). cStepsS.
    cForceS ((Val.Vptr loc)↑). cForcesS. iFrame.
    iSplitL "Hinv".
    { iSplit; first done. iExists (Val.Vptr loc); iSplit; first done.
      rewrite /stack_handle /stack_inv.
      iExists loc, γinv, γh, γslot,
        (Cell.singleton (Message.message (Val.Vptr (loc >> 2)) Vh nah) LTh),
        (Cell.singleton (Message.message (Val.Vptr (loc >> 2)) Vo nao) LTo),
        γguard, (Cell.singleton (Message.message Val.zero Vg nag) LTg), γnm.
      iSplit; first (iPureIntro; split; done). iFrame "Hinv SNh SNo SNg". }
    cStepsS. cStepsT. cStep. iFrame. done.
  Qed.
End StackIM.
