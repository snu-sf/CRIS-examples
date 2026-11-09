Require Import CRIS.common.CRIS.
From CRIS.filter Require Import CallFilter.
From CRIS.proofmode Require Import BiEnrichedProset.
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
  Local Notation StackHelpM := (StackM.t mn ★ HelpingOn).
  Local Notation StackM := (StackHelpM ★ MemA ★ SchI).
  Local Notation StackI := ((CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy) ★ MemA ★ SchI).
  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Local Definition Ist : iProp Σ :=
    (IstHelp (IstEq StackHelpM) ⊤ ∗
       IstEq (MemA ★ SchI))%I.

  Local Lemma sim_funs :
    ⊢ ISim.sim_funs open StackM StackI Ist StackHelpM
        (CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy).
  Proof.
    rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - mod_tac.
      }
      iIntros (fn) "%Hfn".
      rewrite Mod.dom_fnsems_add in Hfn.
      unfold StackM.t, HelpingOn.t in Hfn.
      cbn in Hfn. set_unfold in Hfn; des; subst.
      + iApply (new_stack_simF mn sp Ist).
      + iApply (push_simF mn sp).
      + iApply (pop_simF mn sp).
      + cStartFunSim; cStepsT; ss.
      + cStartFunSim; cStepsT; ss.
  Qed.

  End SIM_FUNS.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : hinv_ownE ⊤ ⊢ ISim.t open StackM StackI.
  Proof.
    iIntros "HE".
    iApply (ISim_reflR open StackHelpM
      (CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy)
      (MemA ★ SchI) (λ STATE, IstHelp (@IstEq Σ STATE StackHelpM) ⊤)
      with "[HE] []").
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT".
      rewrite /IstHelp. iFrame "HE".
      iApply (state_eq_init_same with "SRC TGT").
    - iIntros (STATE). iApply sim_funs.
  Qed.
End StackIM. End StackIM.

From CRIS.helping Require Export HelpingFacts.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !stackGS}.

  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.
  Context (mn : string) (sp : specmap).

  Local Notation Ctx :=
    (CFilter.filter (Helping.exports mn) (MemA.t sp) ★
      CFilter.filter (Helping.exports mn) SchI.t).
  Local Definition Ist : iProp Σ :=
    (state_init_tgt ({[mn]} : gset string) ∅ STATE ∗ IstEq Ctx)%I.

  Local Lemma sim_funs_off :
    ⊢ ISim.sim_funs open (StackA.t ★ Ctx)
        ((StackM.t mn ★ HelpingOff.t mn StackM.jobCode) ★ Ctx)
        Ist StackA.t (StackM.t mn ★ HelpingOff.t mn StackM.jobCode).
  Proof.
    rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - mod_tac.
      }
      iIntros (fn) "%Hfn".
      unfold StackA.t in Hfn. cbn in Hfn.
      set_unfold in Hfn; des; subst.
    + cStartFunSim. rewrite /StackM.new_stack /StackA.new_stack. cStepsS; cStepsT.
      aStepS (N n) "[%v ->]".
      aForceT N with ""; eauto. sYields. destruct _q as [? []]; cStepsT.
      sYieldS. cForceS (_, tt). cStepsS.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
      iFrame; auto.
    + cStartFunSim. rewrite /StackM.push /StackA.push. cStepsS; cStepsT.
      aStepS (N [v γs]) "[%s [-> [%n #Hstack]]]".
      aForceT N with ""; try instantiate (1:=(_, _)); first simpl; eauto.
      cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT.
      aUnfoldS. aUnfoldT. sYields. sYieldS. cStepsS.
      rewrite /StackM.jobCode. cForcesT; iFrame.
      cStepsT. cForceS (inr _). cForcesS; iFrame.
      sYields. sYieldS. cStepsS.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
      eauto with iFrame.
    + cStartFunSim. rewrite /StackM.pop /StackA.pop. cStepsS; cStepsT.
      aStepS (N γs) "[%s [-> [%n #Hstack]]]".
      aForceT N with ""; first eauto with iFrame.
      aAddY. sYields. case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. cStepsT.
        sYields. sYieldS.
        aStep. iExists 0. iAuIntro. iAaccIntro "% $ !>" with "". iSplit; first eauto.
        iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
        iIntros "IST". cStepsT. sYieldS. cStepsS.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
      eauto with iFrame.
      }
      cStepsT. sYieldS. aStep.
      iExists 0. iAuIntro. iAaccIntro "% $ !>" with "". iSplit; first eauto.
      iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
      iIntros "IST". cStepsT. sYieldS.
      cStepsS.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
      eauto with iFrame.
  Qed.

  End SIM_FUNS.

  Lemma ctxr (sp : specmap) :
    help_init_cond ⊢
      ctx_refines
        (StackI.t ★ MemA.t sp ★ SchI.t)
        (StackA.t ★ MemA.t sp ★ SchI.t).
  Proof.
    iIntros "H".
    iApply
      (helping_main StackM.t StackA.t StackI.t (MemA.t sp)
        StackM.jobCode with "H").
    { iIntros (mn) "HE". rewrite !CFilter.filter_app.
      (* intermediate refinement with helping facilities *)
      rewrite comm assoc (comm _ (HelpingDummy.t mn)).
      jIntros (ctx_refines_BiProset)
        "((STACK & DUMMY) & MEM & SCH)".
      jPoseProof main_adequacy
        with "[HE]" "[STACK DUMMY MEM SCH]" as "DST".
      { iApply (StackIM.sim mn sp). iFrame. }
      { jFrame "STACK DUMMY MEM SCH". }
      jDestruct "DST" as "((STACK & HELP) & MEM & SCH)".
      jFrame "STACK MEM SCH HELP".
    }

    iIntros (mn). rewrite !CFilter.filter_app.
    jIntros (ctx_refines_BiProset)
      "(STACK & ((MEM & SCH) & HELP))".
    iAssert
      (ctx_refines
        ((StackM.t mn ★ HelpingOff.t mn StackM.jobCode) ★
          CFilter.filter (Helping.exports mn) (MemA.t sp) ★
          CFilter.filter (Helping.exports mn) SchI.t)
        (StackA.t ★
          CFilter.filter (Helping.exports mn) (MemA.t sp) ★
          CFilter.filter (Helping.exports mn) SchI.t))%I
      as "REF".
    { iApply main_adequacy.
    iStopProof.
    iIntros "_".
    iApply (ISim_reflR open StackA.t
      (StackM.t mn ★ HelpingOff.t mn StackM.jobCode)
      (CFilter.filter (Helping.exports mn) (MemA.t sp) ★
      CFilter.filter (Helping.exports mn) SchI.t)
      (λ STATE, state_init_tgt ({[mn]} : gset string) ∅ STATE)).
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro.
        unfold StackA.t, StackM.t, HelpingOff.t; cbn.
        apply submseteq_nil_l.
      }
      iIntros "SRC TGT".
      assert (Hscopes :
        list_to_set
          (Mod.scopes (StackM.t mn ★ HelpingOff.t mn StackM.jobCode)) =
        ({[mn]} : gset string)).
      { apply set_eq. intros scope.
        unfold Mod.add; cbn.
        unfold StackM.t, HelpingOff.t; cbn. set_solver. }
      assert (Hinit :
        Mod.initial_st (StackM.t mn ★ HelpingOff.t mn StackM.jobCode) = ∅).
      { unfold Mod.add, StackM.t, HelpingOff.t; cbn.
        apply map_eq. intros key. rewrite lookup_union_with. simpl_map.
        reflexivity. }
      iEval (rewrite Hscopes Hinit) in "TGT".
      iExact "TGT".
    - iIntros (STATE). iApply sim_funs_off.
    }
    jApply "REF".
    jFrame.
  Qed.
End StackIA. End StackIA.
