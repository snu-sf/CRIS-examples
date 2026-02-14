Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.

Module CannonIA. Section CannonIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.
  Import CannonA.

  Context (sp : specmap).

  Definition Ist : ist_type Σ :=
    (λ st_s st_t, (⌜st_t = {[CannonI.v_lv := Some 1%Z↑]}⌝ ∗ Ready) ∨ Fired)%I.
  
  Local Definition CannonAMod := (CannonA.t sp).
  Local Definition CannonIMod := (CannonI.t).

  Lemma simF_fire : ISim.sim_fun open CannonAMod CannonIMod Ist (Some CannonHdr.fire).
  Proof using.
    iStartSim.

    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "(-> & -> & B)". hss.
    iDestruct "IST" as "[[% R] | F]"; des; subst; cycle 1. 
    (* already fired *)
    { iExFalso. iApply FiredBall; iFrame. }

    steps_l. steps_r. hss. steps_r.
    change (1 `div` 1)%Z with 1%Z.

    (* SRC, TGT: print 1 *)
    step. steps_r.

    (* prove postcondition & the IST - Ready * Ball = Shot *)
    steps_l. forces_l. iSplitR; eauto. step.
    iSplit; eauto. iRight. iApply ReadyBall; iFrame.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open CannonAMod CannonIMod CannonA.Ready Ist.
  Proof using.
    init_sim.
    - iIntros "IC"; iLeft; iFrame; eauto.
    - eapply simF_fire.
  Qed.
End CannonIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Lemma ctxr (sp : specmap) :
    ctx_refines (CannonA.t sp, CannonA.Ready) (CannonI.t, emp%I).
  Proof using. eapply main_adequacy, sim. Qed.
End ctxr. End CannonIA.
