Require Import CRIS.common.CRIS.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.imp_system Require Import mem.MemTactics mem.MemA.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.elimination_stack Require Import StackHeader StackA StackI.
From CRIS.elimination_stack Require Import StackIANewStack StackIAPush.
From CRIS.elimination_stack Require Import StackIAPop.
From CRIS.helping Require Export HelpingTactics.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !stackGS}.

  (* Helping module being parameterized by mn *)
  Context (mn : string).
  Context (sp : specmap).

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn StackM.jobCode).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := ((StackM.t mn ★ HelpingOn) ★ MemA ★ SchI).
  Local Notation StackI := ((CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy) ★ MemA ★ SchI).
  Local Notation Ist := (IstProd (IstSB [mn] (IstHelp IstTrue ⊤)) IstEq).

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI (hinv_ownE ⊤) Ist.
  Proof.
    cStartModSim.
    { apply new_stack_simF. }
    { apply push_simF. }
    { apply pop_simF. }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    { iIntros "HE". rewrite /IstProd /IstSB /IstHelp /IstTrue /IstEq.
      repeat iExists _; iFrame; iPureIntro; splits; eauto; ss. }
  Qed.
End StackIM. End StackIM.

From CRIS.helping Require Export HelpingFacts.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !stackGS}.

  Lemma ctxr (sp : specmap) :
    help_init_cond ⊢
      ctx_refines
        (StackI.t ★ MemA.t sp ★ SchI.t)
        (StackA.t ★ MemA.t sp ★ SchI.t).
  Proof.
    iIntros "H". iApply (helping_main with "H").
    { iIntros (mn) "HE". rewrite !CFilter.filter_app.
      (* intermediate refinement with helping facilities *)
      rewrite comm assoc (comm _ (HelpingDummy.t mn)).
      iApply ctxr_trans. iSplitL "HE".
      { iApply main_adequacy.
        - apply StackIM.sim.
        - iExact "HE".
      }
      rewrite -!assoc. iApply ctxr_trans. iSplitR.
      { ctxr_rotate. ctxr_swap. do 2 ctxr_rotate. ctxr_swap. ctxr_rotate. ctxr_swap.
        do 3 ctxr_rotate. ctxr_refl.
      }
      ctxr_refl.
    }

    iIntros (mn). rewrite !CFilter.filter_app.
    iApply ctxr_trans. iSplitR.
    { do 3 ctxr_rotate. ctxr_swap. ctxr_refl. }
    rewrite (assoc _ (StackM.t mn)).

    iApply (main_adequacy _ _ emp%I
      (IstProd (IstSB (Mod.scopes StackA.t ++ [mn]) IstTrue) IstEq)).
    cStartModSim.
    { cStartFunSim. rewrite /StackM.new_stack /StackA.new_stack. cStepsS; cStepsT.
      aStepS (N n) "[%v ->]".
      aForceT N with ""; eauto. sYields. destruct _q as [? []]; cStepsT.
      sYieldS. cForceS (_, tt); cStep; iFrame; auto.
    }
    { cStartFunSim. rewrite /StackM.push /StackA.push. cStepsS; cStepsT.
      aStepS (N [v γs]) "[%s [-> [%n #Hstack]]]".
      aForceT N with ""; try instantiate (1:=(_, _)); first simpl; eauto.
      cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT.
      aUnfoldS. aUnfoldT. sYields. sYieldS. cStepsS.
      rewrite /StackM.jobCode. cForcesT; iFrame.
      cStepsT. cForceS (inr _). cForcesS; iFrame.
      sYields. sYieldS. cStep; eauto with iFrame.
    }
    { cStartFunSim. rewrite /StackM.pop /StackA.pop. cStepsS; cStepsT.
      aStepS (N γs) "[%s [-> [%n #Hstack]]]".
      aForceT N with ""; first eauto with iFrame.
      aAddY. sYields. case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. cStepsT.
        sYields. sYieldS.
        aStep. iExists 0. iAuIntro. iAaccIntro "% $ !>" with "". iSplit; first eauto.
        iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
        clear_st; iIntros (st_src st_tgt) "IST". cStepsT. sYieldS. cStep; eauto with iFrame.
      }
      cStepsT. sYieldS. aStep.
      iExists 0. iAuIntro. iAaccIntro "% $ !>" with "". iSplit; first eauto.
      iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
      clear_st; iIntros (st_src st_tgt) "IST". cStepsT. sYieldS. 
      cStep; eauto with iFrame.
    }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
    iEmpIntro.
  Qed.
End StackIA. End StackIA.
