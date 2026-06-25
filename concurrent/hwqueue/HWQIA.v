Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics HelpingFacts SchI SchTactics.
Require Import HWQI HWQP HWQA HWQIANewQueue HWQIAEnqueue HWQIADequeue.

Module HWQPM. Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mnh mnp : string).
  Context (sp_mem : specmap).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (∃ (X : gset val),
      free_id (λ x, x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type ∗
      [∗ set] x ∈ X, ∃ ptr ofs, ⌜x = Vptr (ptr, ofs)⌝ ∗ ∃ v, (ptr, ofs) ↦{1/2} v)%I.
  Definition IstFull : ist_type Σ := IstHelp_gen Ist mnh ⊤.

  Notation HWQM := (HWQM.t mnh).
  Notation HWQP := (HWQP.t mnp).
  Notation HelpOn := (HelpingOn.t mnh HWQM.jobCode).
  Notation HelpDummy := (HelpingDummy.t mnh).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mnp ∅).

  Lemma ctxr :
    ctx_refines
      ((HWQP ★ HelpDummy) ★ MemA ★ ProphA, emp)%I
      ((HWQM ★ HelpOn)    ★ MemA ★ ProphA, help_init_cond ∗ free_id top1)%I.
  Proof.
    eapply main_adequacy with (Ist := IstFull).
    cStartModSim.
    { apply simF_new_queue. }
    { apply simF_enqueue. }
    { apply simF_dequeue. }
    { cStartFunSim. cStepsT; ss. }
    { cStartFunSim. cStepsT; ss. }
    { iIntros "[[$ $] F]"; iExists _, _, _, _; repeat iSplit; eauto.
      { iPureIntro; set_unfold. intros x [[? ?] [-> Hx]]; ss.
        rewrite dom_union_with dom_empty left_id in Hx; set_unfold; inv Hx; left; done.
      }
      iExists ∅; iSplit; eauto.
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
    ctx_refines
      (HWQM.t mnh ★ ProphecyA.t mnp ∅ ★ HelpingOff.t mnh HWQM.jobCode, emp%I)
      (HWQA.t, emp%I).
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
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !hwqGS, !memGS, !prophGS}.

  Lemma ctxr (ctx : Mod.t) (sp_mem : specmap) genv :
    real_mod ctx →
    refines
      (HWQI.t ★ MemI.t genv   ★ SchI.t ★ ctx,
        emp%I)
      (HWQA.t ★ MemA.t sp_mem ★ SchI.t ★ ctx,
        MemA.init_cond genv ∗ ProphecyA.initial_cond ∗ help_init_cond ∗ free_id top1)%I.
  Proof.
    intros Hreal.
        set (allmds := HWQA.t ★ MemA.t sp_mem ★ HWQI.t ★ MemI.t genv ★ SchI.t ★ ctx).
    set (sz := S (max
                 (maxlen (elements (get_fids (dom (Mod.fnsems allmds)))))
                 (maxlen (Mod.scopes allmds)))).
    etrans.
    { rewrite assoc.
      eapply prophecy_refines with (sz:=sz) (mdm := λ mn, HWQP.t mn ★ MemI.t genv).
      { intros Q. rewrite !CFilter.filter_app.
        etrans.
        { eapply ctxr_refines.
          ctxr_rotate. ctxr_drop. ctxr_rotate. do 2 ctxr_drop.
          rewrite HWQI.filter_prophecy. apply HWQIP.ctxr. }
        rewrite MemI.filter_prophecy.
        evar_at_last_1; [refl|f_equal]. mod_eq_solver.
      }
      { intros Q. etrans.
        { eapply ctxr_refines. do 2 ctxr_rotate. do 3 ctxr_drop. apply MemIA.ctxr. }
        etrans.
        { rewrite comm -assoc comm.
          eapply helping_refines
            with (mA := HWQA.t ★ MemA.t sp_mem)
                 (mM := λ mnh, HWQM.t mnh ★ MemA.t sp_mem ★ ProphecyA.t _ ∅).
          - intros Q0 mnh. eapply ctxr_refines. etrans.
            { do 2 rewrite CFilter.filter_app.
              rewrite HWQP.filter_helping MemA.filter_helping ProphecyA.filter_helping.
              do 3 ctxr_rotate. ctxr_drop. ctxr_swap. rewrite assoc. eapply HWQPM.ctxr.
            }
            evar_at_last_1; [refl|f_equal]. mod_eq_solver.
          - intros Q0 mnh. eapply ctxr_refines. etrans.
            { ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
              eapply HWQMA.ctxr; et.
            }
            evar_at_last_1; [refl|f_equal]. mod_eq_solver.
          - intros fn IN1 IN2. subst sz allmds.
            rewrite -elem_of_elements in IN1. eapply elem_of_maxlen in IN1.
            eapply prophecy_exports_long in IN2. rewrite mname_long_length in IN2.
            do 3 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in IN1.
            do 5 rewrite Mod.dom_fnsems_add maxlen_get_fids_union in IN2. nia.
        }
        etrans.
        { eapply ctxr_refines. do 2 ctxr_drop. eapply CFilter.intro_filter. }
        rewrite !left_id !assoc. refl.
      }
      { rewrite -!assoc. et. }
      { eapply Mod.real_mod_add; [apply HWQP.real_mod|apply MemI.real]. }
      { eapply Mod.real_mod_add; et. apply SchI.real. }
    }
    rewrite !left_id -!assoc.
    eapply ctxr_refines, ctxr_consequence. iIntros "[$ $]".
  Qed.
End HWQIA. End HWQIA.
