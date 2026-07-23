Require Import CRIS.common.CRIS.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.system
  Require Import SystemHeader SystemA SystemTactics.
From CRIS.promise_free.elimination_stack
  Require Import StackHeader StackA StackI.
From CRIS.promise_free.elimination_stack
  Require Import StackIANewStack StackIAPush StackIAPop.
From CRIS.helping Require Export HelpingTactics.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I,
    _HIST : !histGS, _ATOMIC : !atomicG, _SYS : !sysGS,
    _STACK : !stackG, _HELP : !helpingGS, _SCH : !schGS}.

  Context (mn : string) (sp_user sp : specmap).

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

  Lemma sim (Hsys : (SystemA.sp sp_user (↑stackN)) ⊆ sp) :
    ISim.t open MA MI (hinv_ownE ⊤) Ist.
  Proof.
    rewrite /MA /MI.
    rewrite -(assoc Mod.add
      (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOn.t mn StackM.jobCode) SysF SchF).
    rewrite -(assoc Mod.add
      (CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn) SysF SchF).
    cStartModSim.
    { rewrite !assoc. exact (new_stack_simF mn sp_user sp). }
    { rewrite !assoc. exact (push_simF mn sp_user sp). }
    { rewrite !assoc. exact (pop_simF mn sp_user sp). }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    all: try mod_tac.
    { iIntros "HE". rewrite /IstProd /IstSB /IstHelp /IstTrue /IstEq.
      repeat iExists _; iFrame; iPureIntro; splits; eauto; ss. }
  Qed.
End StackIM. End StackIM.

From CRIS.helping Require Export HelpingFacts.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I,
    _HIST : !histGS, _ATOMIC : !atomicG, _SYS : !sysGS,
    _STACK : !stackG, _HELP : !helpingGS, _SCH : !schGS}.

  Lemma ctxr (sp_user sp : specmap) :
    (SystemA.sp sp_user (↑stackN)) ⊆ sp →
    help_init_cond ⊢
      ctx_refines
        (StackI.t ★ SystemA.t sp_user (↑stackN) sp ★ SchI.t)
        (StackA.t (SystemA.sp sp_user (↑stackN)) ★
          SystemA.t sp_user (↑stackN) sp ★ SchI.t).
  Proof.
    intros Hsys.
    iIntros "H".
    iApply (helping_main
      (fun mn => StackM.t mn (SystemA.sp sp_user (↑stackN)))
      (StackA.t (SystemA.sp sp_user (↑stackN))) StackI.t
      (SystemA.t sp_user (↑stackN) sp)
      StackM.jobCode with "H").
    { iIntros (mn) "HE". rewrite !CFilter.filter_app.
      (* intermediate refinement with helping facilities *)
      rewrite comm assoc (comm _ (HelpingDummy.t mn)).
      iApply ctxr_trans. iSplitL "HE".
      { rewrite !assoc.
        iApply (main_adequacy _ _ (hinv_ownE ⊤)
          (IstProd (IstSB [mn] (IstHelp IstTrue ⊤)) IstEq)
          (StackIM.sim mn sp_user sp Hsys)).
        iExact "HE".
      }
      rewrite -!assoc. iApply ctxr_trans. iSplitR.
      { ctxr_rotate. ctxr_swap. do 2 ctxr_rotate. ctxr_swap.
        ctxr_rotate. ctxr_swap. do 3 ctxr_rotate. ctxr_refl. }
      rewrite (comm Mod.add
        (HelpingOn.t mn StackM.jobCode)
        (CFilter.filter (Helping.exports mn) SchI.t)).
      rewrite (assoc Mod.add
        (CFilter.filter (Helping.exports mn)
          (SystemA.t sp_user (↑stackN) sp))
        (StackM.t mn (SystemA.sp sp_user (↑stackN)))
        (CFilter.filter (Helping.exports mn) SchI.t ★
          HelpingOn.t mn StackM.jobCode)).
      rewrite (comm Mod.add
        (CFilter.filter (Helping.exports mn)
          (SystemA.t sp_user (↑stackN) sp))
        (StackM.t mn (SystemA.sp sp_user (↑stackN)))).
      rewrite -(assoc Mod.add
        (StackM.t mn (SystemA.sp sp_user (↑stackN)))
        (CFilter.filter (Helping.exports mn)
          (SystemA.t sp_user (↑stackN) sp))
        (CFilter.filter (Helping.exports mn) SchI.t ★
          HelpingOn.t mn StackM.jobCode)).
      ctxr_refl.
    }

    iIntros (mn). rewrite !CFilter.filter_app.
    iApply ctxr_trans. iSplitR.
    { do 3 ctxr_rotate. ctxr_swap. ctxr_refl. }

    rewrite
      (assoc _
        (StackM.t mn (SystemA.sp sp_user (↑stackN)))).

    iApply (main_adequacy _ _ emp%I
      (IstProd
        (IstSB
          (Mod.scopes (StackA.t (SystemA.sp sp_user (↑stackN))) ++ [mn])
          IstTrue)
        IstEq)).
    cStartModSim.
    { (* new_stack *)
      cStartFunSim.
      rewrite /StackM.new_stack /StackA.new_stack /stack_atomic_fun.
      cStepsS. cStepsT.
      destruct _q as [[tid stid] V].
      iDestruct "ASM" as "[-> TV]".
      cForceT (tid, stid, V).
      cForceT (tt↑). cForcesT.
      iFrame "TV". repeat iSplit; eauto.
      iApply wsim_bind. iSplitL "IST".
      { iApply isim_wsim. iIntros "WINV". iApply isim_refl.
        - intros; ss.
        - intros; ss.
        - iFrame. }
      iIntros (????) "[-> IST]".
      sYields. sYieldS.
      iDestruct "GRT" as "[%EQ GRT]".
      subst _q0.
      cForceS (_q↑, tt).
      cForcesS. iFrame "GRT".
      cStep. iFrame. auto.
    }
    { (* push *)
      cStartFunSim.
      rewrite /StackM.push /StackA.push /stack_atomic_fun.
      cStepsS. cStepsT.
      destruct _q as [[[[value γs] tid] stid] V].
      iDestruct "ASM" as (stack) "[-> [#HANDLE TV]]".
      cForceT (value, γs, tid, stid, V).
      cForceT ((stack, value, γs)↑). cForcesT.
      iFrame "HANDLE TV". repeat iSplit; eauto.
      cStepsT.
      cNormS.
      iApply wsim_bind. iSplitL "IST".
      { iApply isim_wsim. iIntros "WINV". iApply isim_refl.
        - intros; ss.
        - intros; ss.
        - iFrame. }
      iIntros (????) "[-> IST]".
      cStepsT.
      cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT.
      aUnfoldS. aUnfoldT. sYields. sYieldS. cStepsS.
      rewrite /StackM.jobCode. cForcesT; iFrame.
      cStepsT. cForceS (inr _). cForcesS; iFrame.
      sYields. sYieldS. cStepsS.
      instantiate (1 := Val.zero↑).
      iDestruct "GRT" as "[-> GRT]".
      cForcesS. iFrame "GRT".
      cStep. iFrame. auto.
    }
    { (* pop *)
      cStartFunSim.
      rewrite /StackM.pop /StackA.pop /stack_atomic_fun.
      cStepsS. cStepsT.
      destruct _q as [[[γs tid] stid] V].
      cStepsS.
      iDestruct "ASM" as "[%stack [-> [#HANDLE TV]]]".
      cForceT (γs, tid, stid, V). cForcesT.
      iSplitL "TV".
      { iExists stack. iFrame "HANDLE TV". eauto. }
      aAddY. sYields. case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. cStepsT.
        sYields. sYieldS.
        aStep. iExists 0. iAuIntro.
        iAaccIntro "% $ !>" with "". iSplit; first eauto.
        iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
        clear_st; iIntros (st_src st_tgt) "IST".
        cStepsT. sYieldS. cForcesS; iFrame "GRT".
        cStep. iFrame. auto.
      }
      cStepsT. sYieldS. aStep.
      iExists 0. iAuIntro.
      iAaccIntro "% $ !>" with "". iSplit; first eauto.
      iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
      clear_st; iIntros (st_src st_tgt) "IST".
      cStepsT. sYieldS. cForcesS; iFrame "GRT".
      cStep. iFrame. auto.
    }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
    iEmpIntro.
  Qed.
End StackIA. End StackIA.
