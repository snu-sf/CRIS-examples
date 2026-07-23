Require Export CRIS.common.CRIS.
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

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (∃ (X : gset val),
      free_id (λ x, x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type ∗
      [∗ set] x ∈ X, ∃ ptr ofs, ⌜x = Vptr (ptr, ofs)⌝ ∗ ∃ v, (ptr, ofs) ↦{1/2} v)%I.
  Definition IstFull : ist_type Σ :=
    IstProd (IstSB [mnh] (IstHelp Ist ⊤)) IstEq.

  Notation HWQM := (HWQM.t mnh).
  Notation HWQP := (HWQP.t mnp).
  Notation HelpOn := (HelpingOn.t mnh HWQM.jobCode).
  Notation HelpDummy := (HelpingDummy.t mnh).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mnp ∅).

  Lemma ctxr :
    hinv_ownE ⊤ ∗ free_id top1 ⊢
      ctx_refines
        ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
        ((HWQM ★ HelpOn) ★ MemA ★ ProphA).
  Proof.
    eapply main_adequacy with (Ist := IstFull).
    cStartModSim.
    { apply simF_new_queue. }
    { apply simF_enqueue. }
    { apply simF_dequeue. }
    { cStartFunSim. cStepsT; ss. }
    { cStartFunSim. cStepsT; ss. }
    { iIntros "[HE F]"; iExists ∅, ∅, ∅, ∅; repeat iSplit; eauto.
      iFrame "HE".
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
  Qed.
End HWQPM. End HWQPM.

Module HWQMA. Section HWQMA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mnp mnh : string).
  Context (sp : specmap).

  Lemma ctxr :
    ⊢ ctx_refines
        (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★ HelpingOff.t mnh HWQM.jobCode)
        HWQA.t.
  Proof.
    eapply main_adequacy. instantiate (1:=λ _ _, True%I).
    cStartModSim; ss.
    { cStartFunSim. rewrite /HWQA.new_queue. cStepsS. cStepT.
      aStepS (N [n sz]) "[-> %Hsz]".
      aForceT N with ""; first (instantiate (1:=(_, _)); eauto).
      sYields. case_match; cStepsT; sYieldS; cForceS (_, tt); cStep; iFrame; ss.
    }
    { cStartFunSim. rewrite /HWQA.enqueue /HWQM.enqueue. cStepsS. cStepsT.
      aStepS (N [γq ?]) "A".
      aForceT N with "A"; first (instantiate (1:=(_, _))); simpl; eauto with iFrame.
      cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT. aUnfoldS.
      aUnfoldT. sYields. sYieldS. rewrite /HWQM.jobCode. cStepsS. cForcesT. iFrame. cStepsT.
      cForceS (inr _). cForcesS. iFrame. sYields.
      iApply wsim_reset. cCoind CIH g' __ with st_src st_tgt. iIntros "IST".
      aUnfoldT. cStepsT. case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. cStepsT.
        sYields. cByCoind CIH; iFrame.
      }
      cStepsT. sYields. sYieldS. cStep; iFrame. by iFrame.
    }
    { cStartFunSim. rewrite /HWQA.dequeue. cStepsS. cStepsT.
      aStepS (N ?) "A". aForceT N with "A"; iFrame.
      aStep. iExists 0; iAuIntro; iAaccIntro "% $ !>" with ""; iSplit.
      { iIntros "$ !>"; by iFrame. }
      iIntros (ret_t) "[% [% [? ?]]] !>"; iExists _; iFrame.
      iModIntro; clear_st; iIntros (??) "_".
      cStepsT. sYieldS. cStep; iFrame. done.
    }
  Qed.
End HWQMA. End HWQMA.

Module HWQIA. Section HWQIA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !hwqGS, !memGS, !prophGS}.

  Lemma ctxr (ctx : Mod.t) (sp_mem : specmap) genv :
    real_mod ctx →
    MemA.init_cond genv ∗ ProphecyA.initial_cond ∗ help_init_cond ∗ free_id top1 ⊢
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
      { iApply ctxr_refines. rewrite !CFilter.filter_app.
        rewrite HWQI.filter_prophecy MemI.filter_prophecy.
        rewrite -!assoc.
        rewrite (assoc _ (MemI.t genv) (ProphecyI.t (mname_long sz)) _).
        rewrite (comm _ (MemI.t genv) (ProphecyI.t (mname_long sz))).
        rewrite -(assoc _ (ProphecyI.t (mname_long sz)) (MemI.t genv) _).
        rewrite !assoc. do 3 iApply ctxr_frameR.
        iApply HWQIP.ctxr.
      }
      iSplitL "PROPH"; first iExact "PROPH".
      iApply refines_trans. iSplitL "MEM".
      { iApply ctxr_refines. do 2 ctxr_rotate. do 3 ctxr_drop.
        iApply MemIA.ctxr. iExact "MEM". }
      iApply refines_trans. iSplitL "HELP FREE".
      { rewrite comm -assoc comm.
        iApply (helping_main_filtered _
          (λ mnh,
            HWQM.t mnh ★ MemA.t sp_mem ★ ProphecyA.t (mname_long sz) ∅)
          (HWQA.t ★ MemA.t sp_mem) _ _ HWQM.jobCode with "HELP [FREE]").
        - intros fn IN1 IN2. subst sz allmds.
          rewrite -elem_of_elements in IN1. eapply elem_of_maxlen in IN1.
          eapply prophecy_exports_long in IN2. rewrite mname_long_length in IN2.
          do 3 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in IN1.
          do 5 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in IN2. nia.
        - iIntros (mnh) "HE".
          do 2 rewrite CFilter.filter_app.
          rewrite HWQP.filter_helping MemA.filter_helping ProphecyA.filter_helping.
          match goal with
          | |- context[MemA.t ?sp] => is_evar sp; unify sp sp_mem
          end.
          set (hqp := HWQP.t (mname_long sz)).
          set (hqm := HWQM.t mnh).
          set (hma := MemA.t sp_mem).
          set (hpa := ProphecyA.t (mname_long sz) ∅).
          set (hflt := CFilter.filter
            (Helping.exports mnh ∪ Prophecy.exports (mname_long sz))
            (SchI.t ★ ctx)).
          set (hdummy := HelpingDummy.t mnh).
          set (hon := HelpingOn.t mnh HWQM.jobCode).
          match goal with
          | |- context[ctx_refines ?ms ?mt] =>
              replace ms with (((hqp ★ hdummy) ★ (hma ★ hpa)) ★ hflt)
                by mod_eq_solver;
              replace mt with (((hqm ★ hon) ★ (hma ★ hpa)) ★ hflt)
                by mod_eq_solver
          end.
          iApply ctxr_frameR.
          iApply (HWQPM.ctxr mnh (mname_long sz) sp_mem). iFrame "HE FREE".
        - iIntros (mnh).
          set (hqm' := HWQM.t mnh).
          set (hqa := HWQA.t).
          set (hma' := MemA.t sp_mem).
          set (hpa' := ProphecyA.t (mname_long sz) ∅).
          set (hflt' := CFilter.filter
            (Helping.exports mnh ∪ Prophecy.exports (mname_long sz))
            (SchI.t ★ ctx)).
          set (hoff := HelpingOff.t mnh HWQM.jobCode).
          match goal with
          | |- context[ctx_refines ?ms ?mt] =>
              replace ms with
                ((hqm' ★ (hpa' ★ hoff)) ★ (hma' ★ hflt'))
                by mod_eq_solver;
              replace mt with (hqa ★ (hma' ★ hflt'))
                by mod_eq_solver
          end.
          iApply ctxr_frameR.
          iApply (HWQMA.ctxr (mname_long sz) mnh).
      }
      iApply refines_trans. iSplitR.
      { iApply ctxr_refines. do 2 ctxr_drop.
        iApply (CFilter.intro_filter
          (Prophecy.exports (mname_long sz)) ctx).
      }
      rewrite CFilter.filter_app !assoc.
      iApply ctxr_refines.
      iApply ctxr_frameR. iApply ctxr_frameL.
      iApply (CFilter.intro_filter
        (Prophecy.exports (mname_long sz)) SchI.t).
    }
    rewrite -!assoc.
    iApply refines_refl.
  Qed.
End HWQIA. End HWQIA.
