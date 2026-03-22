Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI StackIAPush StackIAPop StackIANewStack.
Require Export HelpingTactics HelpingFacts.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !stackG StackM.jobID StackM.retID}.
  Local Existing Instances stack_helpingG.

  (* Helping module being parameterized by mn *)
  Context (mn : string).

  (* Stack module being masked for eliminating the helping module *)
  Context (N : namespace) (sp sp_user : specmap).

  Definition init_cond : iProp Σ := helping_auth 1 ∅%I.

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn StackM.jobCode (SchA.sp ∅ (↑N))).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := ((StackM.t mn N (SchA.sp ∅ (↑N)) ★ HelpingOn) ★ MemA ★ SchI).
  Local Notation StackI := ((CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy) ★ MemA ★ SchI).

  Local Notation IstFull := (IstProd (IstSB [mn] (IstHelp mn)) IstEq).

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI init_cond IstFull.
  Proof.
    cStartModSim.
    - apply new_stack_simF.
    - apply push_simF.
    - apply pop_simF.
    - cStartFunSim; cStepsT. cStepsT; ss.
    - cStartFunSim; cStepsT. cStepsT; ss.
    - iIntros "I"; repeat iExists _; iFrame; iPureIntro; splits; eauto; ss.
      + rewrite dom_union_with; set_solver.
      + rewrite left_id_L //.
  Qed.
End StackIM. End StackIM.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS, !stackG StackM.jobID StackM.retID}.

  Lemma ctxr (N : namespace) (sp sp_user : specmap) :
    SchA.sp sp_user (↑N) ⊆ sp →
    ctx_refines
      (StackI.t      ★ MemA.t sp ★ SchI.t, emp%I)
      (StackA.t N sp ★ MemA.t sp ★ SchI.t, StackIM.init_cond).
  Proof.
    intros Hsp.
    etrans; cycle 1; first eapply ctxr_consequence.
    { instantiate (1:=(_ ∗ emp)%I); iIntros "H"; iSplitL; last done; iExact "H". }
    eapply helping_main; i; rewrite !CFilter.filter_app.
    { rewrite (comm _ _ (HelpingOn.t _ _ _)) (assoc _ _ (HelpingOn.t _ _ _)).
      etrans; [|eapply main_adequacy, StackIM.sim].
      rewrite -!assoc. ctxr_drop.
      do 2 ctxr_rotate. refl.
    }
    instantiate (1:= N); s.

    etrans.
    { do 3 ctxr_rotate. ctxr_swap. ctxr_refl. }
    rewrite (assoc _ (StackM.t _ _ _)).

    eapply main_adequacy
      with (Ist := IstProd (IstSB (Mod.scopes (StackA.t N sp) ++ [mn]) IstTrue) IstEq).
    cStartModSim.
    { cStartFunSim. rewrite /StackM.new_stack /StackA.new_stack. cStepsS; cStepsT.
      aStepS; iIntros (mtid stid n) "TID [%v ->]".
      aForceT with "TID"; iExists _; iSplit; first eauto.
      sYieldII "IST". destruct _q as [? []]; cStepsT. sYieldS. cForceS (_, tt); cStep; iFrame.
      iDestruct "GRT" as "[$ [% [% [% [$ $]]]]]"; iModIntro; iSplit; ss.
    }
    { cStartFunSim. rewrite /StackM.push /StackA.push. cStepsS; cStepsT.
      aStepS; iIntros (mtid stid [v γs]) "TID [%s [-> [%n #Hstack]]]".
      aForceT with "TID"; iExists (_, _); iSplit; first by iFrame "#".
      cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT.
      rewrite unfold_atomic_update_sem. sYieldII "IST". sYieldS. cStepsS. cForcesT; iFrame.
      cStepsT. cForceS (inr _). cForcesS; iFrame.
      sYieldII "IST". sYieldS. cStep; iFrame. iDestruct "GRT" as "[TID _]"; iFrame. done.
    }
    { cStartFunSim. rewrite /StackM.pop /StackA.pop. cStepsS; cStepsT.
      aStepS; iIntros (mtid stid γs) "TID [%s [-> [%n #Hstack]]]".
      aForceT with "TID"; iExists _; iSplit; first by iFrame "#".
      iApply atomic_update_sem_prepend_yield_src. sYieldII "IST". case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. sYieldII "IST". sYieldS.
        appendRetS. aStep.
        iExists 0. iAuIntro. iAaccIntro "% $ !>" with "". iSplit; first eauto.
        iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
        clear_st; iIntros (st_src st_tgt) "IST". cStepsT. sYieldS. cStep; iFrame.
        iDestruct "GRT" as "[? ?]"; iFrame; ss.
      }
      cStepsT. sYieldS. appendRetS. aStep.
      iExists 0. iAuIntro. iAaccIntro "% $ !>" with "". iSplit; first eauto.
      iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
      clear_st; iIntros (st_src st_tgt) "IST". cStepsT. sYieldS. cStep; iFrame.
      iDestruct "GRT" as "[? ?]"; iFrame; ss.
    }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.
End StackIA. End StackIA.
