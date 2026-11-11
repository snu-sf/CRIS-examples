From CRIS.common Require Import CRIS.
From CRIS.filter Require Import CallFilter.
From CRIS.proofmode Require Import BiEnrichedProset.
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
  Local Definition StackHelpM :=
    StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
      HelpingOn.t mn StackM.jobCode.
  Section SIM_FUNS.
    Context `{STATE : !stateGS Σ}.

  Local Definition Ist : iProp Σ :=
    (IstHelp (IstEq StackHelpM) ⊤ ∗
      IstEq (SysF ★ SchF))%I.

  Local Lemma sim_fun (Hsys : (SystemA.sp sp_user (↑stackN)) ⊆ sp)
      fn (Hfn : fn ∈ dom (Mod.fnsems StackHelpM)) :
    ⊢ ISim.sim_fun open (StackHelpM ★ (SysF ★ SchF))
        ((CFilter.filter (Helping.exports mn) StackI.t ★
            HelpingDummy.t mn) ★ (SysF ★ SchF)) Ist fn.
  Proof.
    rewrite Mod.dom_fnsems_add in Hfn.
    unfold StackM.t, HelpingOn.t in Hfn.
    cbn in Hfn. set_unfold in Hfn; des; subst.
    + rewrite !assoc. iApply (new_stack_simF mn sp_user sp).
    + rewrite !assoc. iApply (push_simF mn sp_user sp).
    + rewrite !assoc. iApply (pop_simF mn sp_user sp).
    + cStartFunSim; cStepsT; ss.
    + cStartFunSim; cStepsT; ss.
  Qed.

  End SIM_FUNS.

  Lemma sim (Hsys : (SystemA.sp sp_user (↑stackN)) ⊆ sp) :
    hinv_ownE ⊤ ⊢ ISim.t open MA MI.
  Proof.
    iIntros "HE".
    rewrite /MA /MI /StackHelpM.
    rewrite -(assoc Mod.add
      (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOn.t mn StackM.jobCode) SysF SchF).
    rewrite -(assoc Mod.add
      (CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn) SysF SchF).
    iApply (ISim_reflR open StackHelpM
      (CFilter.filter (Helping.exports mn) StackI.t ★
        HelpingDummy.t mn)
      (SysF ★ SchF) (fun STATE =>
        IstHelp (@IstEq Σ STATE StackHelpM) ⊤) with "[HE] []").
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT".
      rewrite /IstHelp. iFrame "HE".
      iApply (state_eq_init_same with "SRC TGT").
    - iIntros (STATE). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - mod_tac.
      }
      iIntros (fn) "%Hfn". iApply sim_fun; eauto.
  Qed.
End StackIM. End StackIM.

From CRIS.helping Require Export HelpingFacts.

Module StackIA. Section StackIA.
  #[local] Typeclasses Opaque stack_atomic_fun.

  Context `{!crisG Γ Σ α β τ _S _I,
    _HIST : !histGS, _ATOMIC : !atomicG, _SYS : !sysGS,
    _STACK : !stackG, _HELP : !helpingGS, _SCH : !schGS}.

  Section SIM_FUNS.
    Context (mn : string) (sp_user sp : specmap).
    Context `{STATE : !stateGS Σ}.

    Local Definition Common :=
      CFilter.filter (Helping.exports mn) (SystemA.t sp_user (↑stackN) sp) ★
        CFilter.filter (Helping.exports mn) SchI.t.
    Local Definition MA := StackA.t (SystemA.sp sp_user (↑stackN)) ★ Common.
    Local Definition MI :=
      (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOff.t mn StackM.jobCode) ★ Common.
    Local Definition Ist : iProp Σ :=
      state_init_tgt ({[mn]} : gset string) ∅ STATE.
    Local Definition IstFull : iProp Σ := (Ist ∗ IstEq Common)%I.

  Local Lemma stack_atomic_fun_src {X X2 : Type}
      (P : X → iProp Σ)
      (body : X → itree crisE (Any.t * X2))
      (Q : X → X2 → Any.t → iProp Σ)
      (fls flt : gmap fname fbody)
      (Ist : iProp Σ) (E1 E2 : coPset)
      g R_t RR ps pt (msk_s : emask) (sp_s : specmap) itt :
    (∀ x,
      P x -∗
      wsim fls flt Ist (E1 ∪ ↑stackN, E2 ∪ ↑stackN) g _ R_t
        (λ rets rett,
          o=> winv (E1 ∪ ↑stackN, E2 ∪ ↑stackN) ∗
            Q x rets.2 rets.1 ∗ RR rets.1 rett)
        true pt
        (⇓sbox(msk_s) (⇓smod(sp_s) (body x))) itt) -∗
    wsim fls flt Ist (E1, E2) g Any.t R_t RR ps pt
      (⇓sbox(msk_s) (⇓smod(sp_s) (stack_atomic_fun P body Q))) itt.
  Proof.
    iIntros "SIM". rewrite /stack_atomic_fun.
    cNormS. case_match; cStepsS; ss. case_match; cStepsS; ss.
    iPoseProof ("SIM" with "ASM") as "SIM".
    appendRetT. wbind _ "SIM" as ([ret_s x2_s] ret_t) ">[W [Q RR]]".
    iApply wsim_fold; iFrame.
    cForceS. iFrame. cStep; iFrame.
  Qed.

  Local Lemma simF_new_stack :
    ⊢ ISim.sim_fun open MA MI IstFull (fid StackHdr.new_stack).
  Proof.
    cStartFunSim.
    rewrite /StackM.new_stack /StackA.new_stack.
    cStepS.
    cStepsT.
    iApply stack_atomic_fun_src.
    iIntros ([[tid stid] V]) "[-> TV]".
    cForceT (tid, stid, V).
    cForceT (tt↑). cForcesT.
    iFrame "TV". repeat iSplit; eauto.
    cStepsT.
    cNormS. cNormT.
    iApply wsim_bind_strong.
    iApply isim_wsim. iIntros "WINV".
    iApply (isim_mono _ _ _ _ _ _
      (fun x y : () => (winv (∅, ∅) ∗ ist_with_eq _ x y)%I)
      _ _ _).
    - iIntros (ret_s ret_t) "[WINV [-> IST]]". iFrame "WINV".
      sYields. sYieldS.
      iDestruct "GRT" as "[%EQ GRT]".
      subst _q0.
      cForceS (_q↑, tt).
      cForcesS.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
      iFrame "WINV GRT IST". auto.
    - iApply isim_frame. iSplitL "WINV"; first iFrame.
      iApply isim_refl.
      + intros; ss.
      + intros; ss.
      + iFrame "IST".
  Qed.

  Local Lemma simF_push :
    ⊢ ISim.sim_fun open MA MI IstFull (fid StackHdr.push).
  Proof.
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
    iIntros (??) "[-> IST]".
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
  Qed.

  Local Lemma simF_pop :
    ⊢ ISim.sim_fun open MA MI IstFull (fid StackHdr.pop).
  Proof.
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
      iIntros "IST".
      cStepsT. sYieldS. cForcesS; iFrame "GRT".
      cStep. iFrame. auto.
    }
    cStepsT. sYieldS. aStep.
    iExists 0. iAuIntro.
    iAaccIntro "% $ !>" with "". iSplit; first eauto.
    iIntros "%ret_t $ !>"; iExists ret_t; iModIntro.
    iIntros "IST".
    cStepsT. sYieldS. cForcesS; iFrame "GRT".
    cStep. iFrame. auto.
  Qed.

  End SIM_FUNS.

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
      jIntros (ctx_refines_BiProset) "((STACK & DUMMY) & SYS & SCH)".
      jPoseProof main_adequacy with "[HE]" "[STACK DUMMY SYS SCH]" as "M".
      { iApply (StackIM.sim mn sp_user sp); et. }
      { jFrame. }
      rewrite /StackIM.MA.
      jDestruct "M" as "[[[STACK HELP] SYS] SCH]".
      jFrame.
    }

    iIntros (mn). rewrite !CFilter.filter_app.
    jIntros (ctx_refines_BiProset)
      "(STACK & ((SYS & SCH) & HELP))".
    iAssert
      (ctx_refines
        ((StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
            HelpingOff.t mn StackM.jobCode) ★
          CFilter.filter (Helping.exports mn)
            (SystemA.t sp_user (↑stackN) sp) ★
          CFilter.filter (Helping.exports mn) SchI.t)
        (StackA.t (SystemA.sp sp_user (↑stackN)) ★
          CFilter.filter (Helping.exports mn)
            (SystemA.t sp_user (↑stackN) sp) ★
          CFilter.filter (Helping.exports mn) SchI.t))%I
      as "REF".
    { iApply main_adequacy.
    iStopProof.
    iIntros "_".
    iApply (ISim_reflR open
      (StackA.t (SystemA.sp sp_user (↑stackN)))
      (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
        HelpingOff.t mn StackM.jobCode)
      (CFilter.filter (Helping.exports mn)
          (SystemA.t sp_user (↑stackN) sp) ★
        CFilter.filter (Helping.exports mn) SchI.t)
      (fun STATE => state_init_tgt ({[mn]} : gset string) ∅ STATE)).
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro.
        unfold StackA.t, StackM.t, HelpingOff.t; cbn.
        apply submseteq_nil_l.
      }
      iIntros "SRC TGT".
      assert (Hscopes :
        list_to_set
          (Mod.scopes
            (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
              HelpingOff.t mn StackM.jobCode)) =
        ({[mn]} : gset string)).
      { apply set_eq. intros scope.
        unfold Mod.add; cbn.
        unfold StackM.t, HelpingOff.t; cbn. set_solver. }
      assert (Hinit :
        Mod.initial_st
          (StackM.t mn (SystemA.sp sp_user (↑stackN)) ★
            HelpingOff.t mn StackM.jobCode) = ∅).
      { unfold Mod.add, StackM.t, HelpingOff.t; cbn.
        apply map_eq. intros key. rewrite lookup_union_with.
        simpl_map. reflexivity. }
      iEval (rewrite Hscopes Hinit) in "TGT".
      iExact "TGT".
    - iIntros (STATE). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - mod_tac.
      }
      iIntros (fn) "%Hfn".
      unfold StackA.t in Hfn. cbn in Hfn.
      set_unfold in Hfn; des; subst.
      + iApply simF_new_stack.
      + iApply simF_push.
      + iApply simF_pop.
    }
    jApply "REF".
    jFrame "STACK HELP SYS SCH".
  Qed.
End StackIA. End StackIA.
