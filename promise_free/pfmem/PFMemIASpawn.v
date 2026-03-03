Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section spawn.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Lemma simF_spawn : ISim.sim_fun open MA MI Ist (fid PFMemHdr.spawn).
  Proof.
    cStartFunSim. rewrite /PFMemI.spawn. cStepsS. destruct _q as [tid V].
    iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as "[% [% [% [[-> [% [% [%WF [% [%PFG %PFL]]]]]] [HA [TA HFA]]]]]]".
    cStepsT. destruct _q as [tid_new Hnin].
    iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND %]]]"; rewrite FIND. cStepsT.
    subst V.
    iMod (tview_auth_alloc _ tid_new with "TA") as "[TA TVnew]"; eauto.
    { rewrite IdentMap.mem_find in Hnin; des_ifs; eauto. }
    cForceS (tid_new↑). cStepsS. cForceS (tid_new↑). cStepsS.
    remember {[_ := _]} as st_tgt'.
    iAssert (Ist st_src st_tgt')%I with "[- TV TVnew]" as "IST".
    { iExists _, _, _; iSplit; first iPureIntro.
      { split; first subst; ss.
        split; eauto.
        split; eauto.
        split.
        { inv WF; econs; ss. eapply Threads.spawn_wf; eauto. }
        split; ss.
        split; ss.
        intros ???; rewrite IdentMap.gsspec; des_ifs; last by apply PFL.
        case; intros -> <-; econs; ss.
      }
      iFrame.
    }
    cForceS. iSplitR "IST".
    { iFrame. eauto. }
    cStepsS. cStep. iSplitR; done.
  (*SLOW*)Qed.
End spawn.
