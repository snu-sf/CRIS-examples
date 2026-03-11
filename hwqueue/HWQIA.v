Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics SchI SchTactics.
Require Import HWQI HWQP HWQA HWQIANewQueue HWQIAEnqueue HWQIADequeue.

Module HWQPM. Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !memGS, !prophGS, !schGS, !hwqG}.
  Context (mn : string).
  Context (N : namespace) (sp_mem : specmap).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (IstHelp mn st_src st_tgt ∗
    ∃ (X : gset val),
      free_id (λ x, (x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type) ∗
      [∗ set] x ∈ X,
        □ ∃ blk ofs nx, ⌜x = Vptr (blk, ofs)⌝ ∗
          ∀ X, helping_auth 1 X =| nx, ↑N |={↑N, ∅}=∗ ∃ v, (blk, ofs) ↦ v)%I.
  Definition IstFull : ist_type Σ :=
    IstProd (IstSB (Mod.scopes (HWQP.t mn) ++ Mod.scopes (HelpingDummy.t mn)) Ist) IstEq.

  Notation sp := (SchA.sp ∅ (↑N)).
  Notation HWQM := (HWQM.t N mn).
  Notation HWQP := (HWQP.t mn).
  Notation HelpOn := (HelpingOn.t mn HWQM.jobCode sp).
  Notation HelpDummy := (HelpingDummy.t mn).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mn ∅).

  Lemma ctxr :
    ctx_refines
      ((HWQM.t N mn ★ HelpingOn.t mn (HWQM.jobCode) sp) ★ MemA.t sp_mem ★ ProphecyA.t mn ∅,
          helping_auth 1 ∅ ∗ free_id top1)%I
      ((HWQP.t mn   ★ HelpingDummy.t mn)                ★ MemA.t sp_mem ★ ProphecyA.t mn ∅,
          emp)%I.
  Proof.
    eapply main_adequacy with (Ist := IstFull).
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

Module HWQIA. Section HWQIA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !hwqG, !memGS, !prophGS}.

  Lemma ctxr (ctx : Mod.t) (N : namespace) (sp_user sp sp_mem : specmap) csl genv :
    SchA.sp sp_user (↑N) ⊆ sp →
    real_mod ctx →
    refines
      (HWQA.t N sp ★ MemA.t sp_mem   ★ SchI.t ★ ctx,
        MemA.init_cond csl genv ∗ ProphecyA.initial_cond ∗ helping_auth 1 ∅ ∗ free_id top1)%I
      (HWQI.t      ★ MemI.t csl genv ★ SchI.t ★ ctx,
        emp%I).
  Proof.
    intros Hsch Hreal.
    eapply helping_prophecy_refines; eauto.
    { apply HWQIP.ctxr. }
    { intros mn; etrans; cycle 1.
      { rewrite assoc; apply HWQPM.ctxr with (N:=N). }
      rewrite assoc //.
    }
    { intros mn; eapply main_adequacy.
      instantiate (1:=λ _ _, True%I).
      cStartModSim; first done; cStartFunSim; ss.
      { cStepsS. cForcesT. iFrame. cStepsT. destruct Any.downcast; cStepsS; ss.
        rewrite /HWQA.new_queue.
        cStepsT. cStepsS. sYieldII "IST". sYieldS. cForcesS. iFrame. cStep. done.
      }
      { rewrite /HWQA.enqueue /HWQM.enqueue /atomic_body.
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
      }
      { rewrite /HWQA.dequeue /HWQM.dequeue /atomic_body.
        cStepsS. cStepsT. cForcesT. iFrame. cStepsT.
        sYieldII "IST". sYieldS.
        destruct _q as [[? ?] [[[? ?] ?] ?]]. cStepsS. cForcesT; iFrame.
        cStepsT. cForcesS; iFrame. cStepsS.
        sYieldII "IST". sYieldS. cForcesS; iFrame.
        cStep; done.
      }
    }
    { intros mn; rewrite /real_mod.
      let real_tac :=
        (split; ss; intros ??; destruct excluded_middle_informative; ss) in
      mod_tac real_tac.
    }
  Qed.
End HWQIA. End HWQIA.
