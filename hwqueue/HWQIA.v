Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics HelpingFacts SchI SchTactics.
Require Import HWQI HWQP HWQA HWQIANewQueue HWQIAEnqueue HWQIADequeue.

Module HWQPM. Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !memGS, !prophGS, !schGS, !hwqG}.
  Context (mnp mnh : string).
  Context (N : namespace) (sp_mem : specmap).

  Notation sp := (SchA.sp ∅ (↑N)).
  Notation HWQM := (HWQM.t N mnh).
  Notation HWQP := (HWQP.t mnp).
  Notation HelpOn := (HelpingOn.t mnh HWQM.jobCode sp).
  Notation HelpDummy := (HelpingDummy.t mnh).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mnp ∅).

  Lemma ctxr :
    ctx_refines
      ((HWQM ★ HelpOn)     ★ MemA ★ ProphA, helping_auth 1 ∅ ∗ free_id top1)%I
      ((HWQP ★ HelpDummy)  ★ MemA ★ ProphA, emp)%I.
  Proof.
    eapply main_adequacy with (Ist := HWQIAInv.IstFull mnp mnh N).
    cStartModSim.
    { apply simF_new_queue. }
    { apply simF_enqueue. }
    { apply simF_dequeue. }
    { cStartFunSim. cStepsT; ss. }
    { cStartFunSim. cStepsT; ss. }
    { iIntros "[H F]"; iExists _, _, _, _; repeat iSplit; eauto.
      { iPureIntro; set_unfold. intros x [[? ?] [-> Hx]]; ss.
        rewrite dom_union_with dom_empty left_id in Hx; set_unfold; inv Hx; left; done.
      }
      iFrame.
      iSplit.
      { iPureIntro; ss; splits; eauto. rewrite left_id //. }
      iExists ∅; iSplit; eauto.
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
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !memGS, !prophGS, !schGS, !hwqG}.
  Context (mnp mnh : string).
  Context (N : namespace) (sp_user sp : specmap).
  Hypothesis (SchSP: SchA.sp sp_user (↑N) ⊆ sp).
  
  Lemma ctxr:
    ctx_refines
      (HWQA.t N sp, emp%I)
      (HWQM.t N mnh ★ ProphecyA.t mnp ∅ ★ HelpingOff.t mnh HWQM.jobCode (SchA.sp ∅ (↑N)), emp%I).
  Proof.
    eapply main_adequacy. instantiate (1:=λ _ _, True%I).
    cStartModSim; ss.
    - cStartFunSim. rewrite /HWQA.new_queue.
      cStepsS. cForcesT. iFrame. cStepsT. destruct Any.downcast; cStepsS; ss.
      cStepsT. sYieldII "IST". sYieldS. cForcesS. iFrame. cStep. done.
    - cStartFunSim. rewrite /HWQA.enqueue /HWQM.enqueue /atomic_body.
      cStepsS. cStepsT. cForcesT. iFrame. cStepsT.
      destruct _q as [[? ?] [[[[? ?] ?] ?] ?]]. sYieldII "IST".
      cInlineT. cStepsT. rewrite /HelpingOff.run. cStepsT. sYieldII "IST".
      sYieldS. cStepsS. cForcesT. iFrame. cStepsT. cForcesS. iFrame.
      cStepsS. sYieldII "IST".
      iApply wsim_reset.
      cCoind CIH g' __ with st_src st_tgt. iIntros "IST".
      unfoldIterT. cStepsT. case_match.
      { cStepsT. cInlineT. cStepsT. rewrite /HelpingOff.help. cStepsT.
        sYieldII "IST". cByCoind CIH; iFrame.
      }
      cStepsT. sYieldII "IST". sYieldS. cForceS; iFrame. cStep. done.
    - cStartFunSim. rewrite /HWQA.dequeue /HWQM.dequeue /atomic_body.
      cStepsS. cStepsT. cForcesT. iFrame. cStepsT.
      sYieldII "IST". sYieldS.
      destruct _q as [[? ?] [[[? ?] ?] ?]]. cStepsS. cForcesT; iFrame.
      cStepsT. cForcesS; iFrame. cStepsS.
      sYieldII "IST". sYieldS. cForcesS; iFrame.
      cStep; done.
  Qed.

End HWQMA. End HWQMA.

Module HWQIA. Section HWQIA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !hwqG, !memGS, !prophGS}.

  Lemma refines (ctx : Mod.t) (N : namespace) (sp_user sp sp_mem : specmap) csl genv :
    SchA.sp sp_user (↑N) ⊆ sp →
    real_mod ctx →
    refines
      (HWQA.t N sp ★ MemA.t sp_mem   ★ SchI.t ★ ctx,
       MemA.init_cond csl genv ∗ ProphecyA.initial_cond ∗ helping_auth 1 ∅ ∗ free_id top1)%I
      (HWQI.t      ★ MemI.t csl genv ★ SchI.t ★ ctx,
       emp%I).
  Proof.
    intros Hsch Hreal.

    set (allmds := HWQA.t N sp ★ MemA.t sp_mem ★ HWQI.t ★ MemI.t csl genv ★ SchI.t ★ ctx).
    set (sz := S (max
                 (maxlen (elements (get_fids (dom (Mod.fnsems allmds)))))
                 (maxlen (Mod.scopes allmds)))).

    etrans; cycle 1.
    { rewrite assoc.
      eapply prophecy_refines with (sz:=sz) (mdm := λ mn, HWQP.t mn ★ MemI.t csl genv).
      { intros Q. rewrite !CFilter.filter_app.
        etrans; cycle 1.
        { eapply ctxr_refines.
          ctxr_rotate. ctxr_drop. ctxr_rotate. do 2 ctxr_drop.
          rewrite HWQI.filter_prophecy. apply HWQIP.ctxr. }
        rewrite MemI.filter_prophecy.
        evar_at_last_1; [refl|f_equal]. mod_eq_solver.
      }
      { intros Q. etrans; cycle 1.
        { eapply ctxr_refines. do 2 ctxr_rotate. do 3 ctxr_drop. apply MemIA.ctxr. }
        etrans; cycle 1.
        { rewrite comm -assoc comm.
          eapply helping_refines
            with (mA := HWQA.t N sp ★ MemA.t sp_mem)
                 (mM := λ mnh, HWQM.t N mnh ★ MemA.t sp_mem ★ ProphecyA.t _ ∅).
          - intros Q0 mnh. eapply ctxr_refines. etrans; cycle 1.
            { do 2 rewrite CFilter.filter_app.
              rewrite HWQP.filter_helping MemA.filter_helping ProphecyA.filter_helping.
              do 3 ctxr_rotate. ctxr_drop. ctxr_swap. rewrite assoc. eapply HWQPM.ctxr.
            }
            evar_at_last_1; [refl|f_equal]. mod_eq_solver.
          - intros Q0 mnh. eapply ctxr_refines. etrans; cycle 1.
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
        etrans; cycle 1.
        { eapply ctxr_refines. do 2 ctxr_drop. eapply CFilter.intro_filter. }
        rewrite !left_id !assoc. refl.
      }
      { rewrite -!assoc. et. }
      { eapply Mod.real_mod_add; [apply HWQP.real|apply MemI.real]. }
      { eapply Mod.real_mod_add; et. apply SchI.real. }
    }
    rewrite !left_id -!assoc.
    eapply ctxr_refines, ctxr_consequence. iIntros "[$ $]".
  Qed.
End HWQIA. End HWQIA.
