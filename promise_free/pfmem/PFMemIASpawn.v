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

  Lemma simF_spawn : ISim.sim_fun open MA MI Ist (Some PFMemHdr.spawn).
  Proof.
    iStartSim. steps_l. destruct _q as [tid V]. rename _q0 into varg.
    iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as "[% [% [% [[-> [% [% [%WF [% [%PFG %PFL]]]]]] [HA [TA HFA]]]]]]".
    steps_r. destruct _q as [tid_new Hnin].
    iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND %]]]"; rewrite FIND. steps_r.
    subst V.
    iMod (tview_auth_alloc _ tid_new with "TA") as "[TA TVnew]"; eauto.
    { rewrite IdentMap.mem_find in Hnin; des_ifs; eauto. }
    force_l (tid_new↑). steps_l. force_l (tid_new↑). steps_l.
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
    force_l. iSplitR "IST".
    { iFrame. eauto. }
    steps_l. step. iSplitR; done.
  (*SLOW*)Qed.
End spawn.