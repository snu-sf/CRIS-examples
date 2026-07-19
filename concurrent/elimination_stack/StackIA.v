Require Import CRIS.common.CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI.
Require Import StackIANewStack StackIAPush StackIAPop.
From CRIS.helping Require Export HelpingTactics HelpingFacts.

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

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI help_init_cond (IstHelp mn ⊤).
  Proof.
    cStartModSim.
    { apply new_stack_simF. }
    { apply push_simF. }
    { apply pop_simF. }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    { iIntros "[? ?]"; repeat iExists _; iFrame; iPureIntro; splits; eauto; ss.
      { rewrite dom_union_with; set_solver. }
      { exists ∅; rewrite left_id_L right_id_L //=. }
    }
  Qed.
End StackIM. End StackIM.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS}.

  Lemma ctxr (sp : specmap) :
    ctx_refines
      (StackI.t ★ MemA.t sp ★ SchI.t, emp%I)
      (StackA.t ★ MemA.t sp ★ SchI.t, help_init_cond).
  Proof.
    etrans; cycle 1; first eapply ctxr_consequence.
    { instantiate (1:=(_ ∗ emp)%I); iIntros "H"; iSplitL; last done; iExact "H". }
    eapply helping_main; i; rewrite !CFilter.filter_app.
    { (* intermediate refinement with helping facilities *)
      rewrite comm assoc (comm _ (HelpingDummy.t mn)).
      etrans; [eapply main_adequacy, StackIM.sim|].
      rewrite -!assoc. etrans.
      { ctxr_rotate. ctxr_swap. do 2 ctxr_rotate. ctxr_swap. ctxr_rotate. ctxr_swap.
        do 3 ctxr_rotate. refl.
      }
      eapply ctxr_consequence; eauto.
    }

    etrans.
    { do 3 ctxr_rotate. ctxr_swap. ctxr_refl. }
    rewrite (assoc _ (StackM.t mn)).

    eapply main_adequacy
      with (Ist := IstProd (IstSB (Mod.scopes (StackA.t) ++ [mn]) IstTrue) IstEq).
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
  Qed.
End StackIA. End StackIA.
