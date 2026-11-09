Require Export CRIS.common.CRIS.
From CRIS.proofmode Require Import BiEnrichedProset.
From CRIS.imp_system Require Export imp.ImpPrelude.
From CRIS.hwqueue Require Export HWQHeader.
Require Export CRIS.scheduler.SchHeader.
From CRIS.imp_system Require Export mem.MemHeader.
Require Export CRIS.prophecy.ProphecyHeader CRIS.helping.HelpingHeader.
Require Export CRIS.filter.CallFilter.
From CRIS.imp_system Require Export mem.MemA.
Require Export CRIS.scheduler.SchA CRIS.prophecy.ProphecyA.
From CRIS.hwqueue Require Export HWQRA.
From CRIS.imp_system Require Import mem.MemI mem.MemIAproof mem.MemTactics.
From CRIS.prophecy Require Import ProphecyI ProphecyFacts.
From CRIS.helping Require Import HelpingTactics HelpingFacts.
From CRIS.scheduler Require Import SchI SchTactics.
From CRIS.hwqueue Require Import HWQI HWQP HWQA HWQIANewQueue HWQIAEnqueue.
From CRIS.hwqueue Require Import HWQIADequeue.

Module HWQPM. Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mnh mnp : string).
  Context (sp_mem : specmap).

  Notation HWQM := (HWQM.t mnh).
  Notation HWQP := (HWQP.t mnp).
  Notation HelpOn := (HelpingOn.t mnh HWQM.jobCode).
  Notation HelpDummy := (HelpingDummy.t mnh).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mnp ∅).

  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Definition Ist : iProp Σ :=
    (∃ (X : gset val),
      free_id (λ x, x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type ∗
      [∗ set] x ∈ X, ∃ ptr ofs, ⌜x = Vptr (ptr, ofs)⌝ ∗ ∃ v, (ptr, ofs) ↦{1/2} v)%I.

  Definition IstFull : iProp Σ :=
    (IstHelp (Ist ∗ IstEq (HWQM ★ HelpOn)) ⊤ ∗
     IstEq (MemA ★ ProphA))%I.

  Local Lemma sim_funs :
    ⊢ ISim.sim_funs open
        ((HWQM ★ HelpOn) ★ MemA ★ ProphA)
        ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
        IstFull (HWQM ★ HelpOn) (HWQP ★ HelpDummy).
  Proof.
    rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split; mod_tac. }
      iIntros (fn) "%Hfn".
      rewrite Mod.dom_fnsems_add in Hfn.
      unfold HWQM.t, HelpingOn.t in Hfn.
      cbn in Hfn. set_unfold in Hfn; des; subst.
      + iApply simF_new_queue.
      + iApply simF_enqueue.
      + iApply simF_dequeue.
      + cStartFunSim. cStepsT; ss.
      + cStartFunSim. cStepsT; ss.
  Qed.

  End SIM_FUNS.

  Lemma ctxr :
    hinv_ownE ⊤ ∗ free_id (fun _ => True%type) ⊢
      ctx_refines
        ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
        ((HWQM ★ HelpOn) ★ MemA ★ ProphA).
  Proof.
    etrans; last eapply (main_adequacy
      ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
      ((HWQM ★ HelpOn) ★ MemA ★ ProphA)).
    iIntros "[HE F]".
    iApply (ISim_reflR open (HWQM ★ HelpOn) (HWQP ★ HelpDummy)
      (MemA ★ ProphA)
      (λ STATE, IstHelp (Ist ∗ @IstEq Σ STATE (HWQM ★ HelpOn)) ⊤)
      with "[HE F] []").
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT".
      rewrite /IstHelp. iFrame "HE".
      iSplitL "F".
      {
      iExists ∅; rewrite big_sepS_empty right_id.
      iPoseProof (free_id_split with "F") as "[F ?]"; last iApply (free_id_iff with "F"); cycle 1.
      { intros i; split; [intros Hi; split; first done; exact Hi|].
        intros [? ?]; ss.
      }
      { intros x; ss. rewrite /Decision.
        match goal with | |- {?P} + {¬ ?P} =>
          destruct (excluded_middle_informative P)
        end; eauto.
      }
      }
      iApply (state_eq_init_same with "SRC TGT").
    - iIntros (STATE). iApply sim_funs.
  Qed.
End HWQPM. End HWQPM.

Module HWQMA. Section HWQMA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mnp mnh : string).
  Context (sp : specmap).

  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Definition Ist : iProp Σ :=
    state_init_tgt ({[mnh]} : gset string) ∅ STATE.

  Local Lemma simF_new_queue :
    ⊢ ISim.sim_fun open HWQA.t
        (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★
          HelpingOff.t mnh HWQM.jobCode) Ist (fid HWQHdr.new_queue).
  Proof.
    cStartFunSim.
      rewrite /HWQA.new_queue. cStepsS. cStepT.
      aStepS (N [n sz]) "[-> %Hsz]".
      aForceT N with ""; first (instantiate (1:=(_, _)); eauto).
      sYields. case_match; cStepsT; sYieldS; cForceS (_, tt).
      cStepsS. cNormT.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret; iFrame; ss.
  Qed.

  Local Lemma simF_enqueue :
    ⊢ ISim.sim_fun open HWQA.t
        (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★
          HelpingOff.t mnh HWQM.jobCode) Ist (fid HWQHdr.enqueue).
  Proof.
    cStartFunSim.
      rewrite /HWQA.enqueue /HWQM.enqueue. cStepsS. cStepsT.
      aStepS (N [γq ?]) "A".
      aForceT N with "A"; first (instantiate (1:=(_, _))); simpl; eauto with iFrame.
      cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT. aUnfoldS.
      aUnfoldT. sYields. sYieldS. rewrite /HWQM.jobCode. cStepsS. cForcesT. iFrame. cStepsT.
      cForceS (inr _). cForcesS. iFrame. sYields.
      iApply wsim_reset.
      assert (EX : exists coind_n : nat, True) by (exists 0; exact I).
      destruct EX as [coind_n _].
      iAssert (⌜coind_n = coind_n⌝ ∗ Ist)%I with "[IST]" as "LOOP".
      { iFrame. done. }
      cCoind CIH g' __ with coind_n. iIntros "[_ IST]".
      aUnfoldT. cStepsT. case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. cStepsT.
        sYields. specialize (CIH coind_n). cByCoind CIH. iFrame. done.
      }
      cStepsT. sYields. sYieldS. cStepsS. cNormT.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
      iFrame. by iFrame.
  Qed.

  Local Lemma simF_dequeue :
    ⊢ ISim.sim_fun open HWQA.t
        (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★
          HelpingOff.t mnh HWQM.jobCode) Ist (fid HWQHdr.dequeue).
  Proof.
    cStartFunSim.
      rewrite /HWQA.dequeue. cStepsS. cStepsT.
      aStepS (N ?) "A". aForceT N with "A"; iFrame.
      aStep. iExists 0; iAuIntro; iAaccIntro "% $ !>" with ""; iSplit.
      { iIntros "$ !>"; by iFrame. }
      iIntros (ret_t) "[% [% [? ?]]] !>"; iExists _; iFrame.
      iModIntro. iIntros "IST".
      cStepsT. sYieldS. cStepsS. cNormT.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret; iFrame. done.
  Qed.

  End SIM_FUNS.

  Lemma ctxr :
    ⊢ ctx_refines
        (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★ HelpingOff.t mnh HWQM.jobCode)
        HWQA.t.
  Proof.
    iApply (main_adequacy
      (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★
        HelpingOff.t mnh HWQM.jobCode)
      HWQA.t).
    iStopProof.
    cStartModSim (fun STATE : stateGS Σ => Ist (STATE := STATE)).
    { assert (Hscopes :
        list_to_set
          (Mod.scopes
            (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★
              HelpingOff.t mnh HWQM.jobCode)) =
        ({[mnh]} : gset string)).
      { apply set_eq. intros scope.
        unfold Mod.add; cbn.
        unfold HWQM.t, ProphecyA.t, HelpingOff.t; cbn. set_solver. }
      assert (Hinit :
        Mod.initial_st
          (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★
            HelpingOff.t mnh HWQM.jobCode) = ∅).
      { unfold Mod.add, HWQM.t, ProphecyA.t, HelpingOff.t; cbn.
        apply map_eq. intros key. rewrite !lookup_union_with.
        simpl_map. reflexivity. }
      iEval (rewrite Hscopes Hinit) in "TGT".
      iExact "TGT". }
    { iApply simF_new_queue. }
    { iApply simF_enqueue. }
    { iApply simF_dequeue. }
  Qed.
End HWQMA. End HWQMA.

Module HWQIA. Section HWQIA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !hwqGS, !memGS, !prophGS}.

  Lemma ctxr (ctx : Mod.t) (sp_mem : specmap) genv :
    real_mod ctx →
    MemA.init_cond genv ∗ ProphecyA.initial_cond ∗ help_init_cond ∗ free_id (fun _ => True%type) ⊢
      refines
        (HWQI.t ★ MemI.t genv ★ SchI.t ★ ctx)
        (HWQA.t ★ MemA.t sp_mem ★ SchI.t ★ ctx).
  Proof.
    intros Hreal.
    set (allmds := HWQA.t ★ MemA.t sp_mem ★ HWQI.t ★ MemI.t genv ★ SchI.t ★ ctx).
    set (sz := S (max
                 (maxlen (elements (get_fids (dom (Mod.fnsems allmds)))))
                 (maxlen (Mod.scopes allmds)))).
    iIntros "(MEM & PROPH & HELP & FREE)".
    iApply refines_trans. iSplitL "MEM PROPH HELP FREE".
    { rewrite assoc.
      iApply (prophecy_refines sz
        (HWQA.t ★ MemA.t sp_mem) (HWQI.t ★ MemI.t genv) (SchI.t ★ ctx)
        (λ mn, HWQP.t mn ★ MemI.t genv));
        try (rewrite -!assoc; et);
        eauto using Mod.real_mod_add, HWQP.real_mod, MemI.real, SchI.real.
      iSplitR "MEM PROPH HELP FREE".
      { iApply ctxr_refines.
        rewrite !CFilter.filter_app.
        rewrite HWQI.filter_prophecy MemI.filter_prophecy.
        set (schflt := CFilter.filter
          (Prophecy.exports (mname_long sz)) SchI.t).
        set (ctxflt := CFilter.filter
          (Prophecy.exports (mname_long sz)) ctx).
        jIntros (ctx_refines_BiProset)
          "((HWQI & MEMI) & PROPHI & SCH & CTX)".
        jPoseProof (HWQIP.ctxr (mname_long sz))
          with "[HWQI PROPHI]" as "(HWQP & PROPHI)".
        { jFrame. }
        jFrame.
      }
      iSplitL "PROPH"; first iExact "PROPH".
      iApply refines_trans. iSplitL "MEM".
      { instantiate (1 :=
          (HWQP.t (mname_long sz)
             ★ MemA.t sp_mem
             ★ ProphecyA.t (mname_long sz) ∅)
            ★ CFilter.filter
                (Prophecy.exports (mname_long sz)) (SchI.t ★ ctx)).
        iApply ctxr_refines.
        jIntros (ctx_refines_BiProset)
          "(HWQP & MEMI & PROPHA & FLT)".
        jPoseProof (MemIA.ctxr sp_mem genv)
          with "MEM" "MEMI" as "MEMA".
        jFrame.
      }
      iApply refines_trans. iSplitL "HELP FREE".
      { iApply (helping_main_filtered
          (Prophecy.exports (mname_long sz))
          (λ mnh,
            HWQM.t mnh ★ MemA.t sp_mem ★ ProphecyA.t (mname_long sz) ∅)
          (HWQA.t ★ MemA.t sp_mem)
          (HWQP.t (mname_long sz) ★
            MemA.t sp_mem ★ ProphecyA.t (mname_long sz) ∅)
          ctx HWQM.jobCode with "HELP [FREE]").
        - intros fn IN1 IN2. subst sz allmds.
          rewrite -elem_of_elements in IN1. eapply elem_of_maxlen in IN1.
          eapply prophecy_exports_long in IN2. rewrite mname_long_length in IN2.
          do 3 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in IN1.
          do 5 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in IN2. nia.
        - iIntros (mnh) "HE".
          do 2 rewrite CFilter.filter_app.
          rewrite HWQP.filter_helping MemA.filter_helping
            ProphecyA.filter_helping.
          set (hflt := CFilter.filter
            (Helping.exports mnh ∪ Prophecy.exports (mname_long sz))
            (SchI.t ★ ctx)).
          jIntros (ctx_refines_BiProset)
            "((HWQP & MEMA & PROPHA) & FLT & DUMMY)".
          jPoseProof (HWQPM.ctxr mnh (mname_long sz) sp_mem)
            with "[HE FREE]" "[HWQP DUMMY MEMA PROPHA]"
            as "((HWQM & ON) & MEMA & PROPHA)".
          { iFrame. }
          { jFrame. }
          jFrame.
        - iIntros (mnh).
          set (hflt' := CFilter.filter
            (Helping.exports mnh ∪ Prophecy.exports (mname_long sz))
            (SchI.t ★ ctx)).
          jIntros (ctx_refines_BiProset)
            "((HWQM & MEMA & PROPHA) & FLT & OFF)".
          jPoseProof (HWQMA.ctxr (mname_long sz) mnh)
            with "[HWQM PROPHA OFF]" as "HWQA".
          { jFrame. }
          jFrame.
      }
      iApply refines_trans. iSplitR.
      { instantiate (1 :=
          (HWQA.t ★ MemA.t sp_mem)
            ★ SchI.t
            ★ CFilter.filter
                (Prophecy.exports (mname_long sz)) ctx).
        iApply ctxr_refines.
        jIntros (ctx_refines_BiProset)
          "((HWQA & MEMA) & SCH & CTX)".
        jPoseProof
          (CFilter.intro_filter
            (Prophecy.exports (mname_long sz)) ctx)
          with "CTX" as "CTX".
        jFrame.
      }
      rewrite CFilter.filter_app !assoc.
      iApply ctxr_refines.
      set (schflt := CFilter.filter
        (Prophecy.exports (mname_long sz)) SchI.t).
      set (ctxflt := CFilter.filter
        (Prophecy.exports (mname_long sz)) ctx).
      jIntros (ctx_refines_BiProset)
        "(((HWQA & MEMA) & SCH) & CTX)".
      jPoseProof
        (CFilter.intro_filter
          (Prophecy.exports (mname_long sz)) SchI.t)
        with "SCH" as "SCH".
      jFrame.
    }
    rewrite -!assoc.
    iApply refines_refl.
  Qed.
End HWQIA. End HWQIA.
