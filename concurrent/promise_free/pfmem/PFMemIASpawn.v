Require Import CRIS.common.CRIS.
From CRIS.promise_free.pfmem Require Import PFMemHeader PFMemI PFMemA.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.gpfsl Require Import base.
From CRIS.promise_free.model Require Import
  Time TView View Cell Memory Global Time.
From CRIS.promise_free.pfmem Require Import PFMemIAproof.

Section spawn.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Section SIM_FUNS.
    Context `{STATE : !stateGS Σ}.

  Lemma simF_spawn :
    ⊢ ISim.sim_fun open MA MI Ist (fid PFMemHdr.spawn).
  Proof.
    cStartFunSim. rewrite /PFMemI.spawn. cStepsS. destruct _q as [tid V].
    iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as (gl ths Vcut)
      "[[%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]] [HA [TA [HFA CONFIG]]]]".
    cStepsT.
    set (config_any := ((Configuration.mk ths gl)↑ : Any.t)).
    subst config_any.
    cStepsT. destruct _q as [tid_new Hnin].
    iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND %]]]"; rewrite FIND. cStepsT.
    subst V.
    iMod (tview_auth_alloc _ tid_new with "TA") as "[TA TVnew]"; eauto.
    { rewrite IdentMap.mem_find in Hnin; des_ifs; eauto. }
    cForceS (tid_new↑). cStepsS. cForceS (tid_new↑). cStepsS.
    cStepsT.
    iAssert Ist%I with "[- TV TVnew]" as "IST".
    { iExists _, _, _; iSplit; cycle 1.
      { iFrame. }
      iPureIntro.
      split; eauto.
      split; eauto.
      split.
      { inv WF; econs; ss. eapply Threads.spawn_wf; eauto. }
      split; ss.
      split; ss.
      intros ???; rewrite IdentMap.gsspec; des_ifs; last by apply PFL.
      case; intros -> <-; econs; ss.
    }
    cForceS. iSplitR "IST".
    { iFrame. eauto. }
    cStepsS. cStep. iSplitR; done.
  (*SLOW*)Qed.
  End SIM_FUNS.

End spawn.
