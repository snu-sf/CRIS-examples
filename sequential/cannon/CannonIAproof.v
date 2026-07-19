From CRIS.common Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.

Module CannonIA. Section CannonIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.
  Import CannonA.

  Context (sp : specmap).

  Definition Ist : ist_type Σ :=
    (λ st_s st_t, (⌜st_t = {[CannonI.v_lv # 1%Z↑]}⌝ ∗ Ready) ∨ Fired)%I.
  
  Local Definition CannonAMod := (CannonA.t sp).
  Local Definition CannonIMod := (CannonI.t).

  Lemma simF_fire : ISim.sim_fun open CannonAMod CannonIMod Ist (fid CannonHdr.fire).
  Proof using.
    cStartFunSim. rewrite /CannonI.fire /fire.

    (* SRC: precondition *)
    cStepsS. iDestruct "ASM" as "[-> [% [-> [-> B]]]]". cSimpl.
    iDestruct "IST" as "[[% R] | F]"; des; subst; cycle 1. 
    (* already fired *)
    { iExFalso. iApply FiredBall; iFrame. }

    cStepsS. cStepsT. cStepsT.
    change (1 `div` 1)%Z with 1%Z.

    (* SRC, TGT: print 1 *)
    cStep. cStepsT.

    (* prove postcondition & the IST - Ready * Ball = Shot *)
    cStepsS. cForcesS. iSplitR; eauto. cStep.
    iSplit; eauto. iRight. iApply ReadyBall; iFrame.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open CannonAMod CannonIMod CannonA.Ready Ist.
  Proof using.
    cStartModSim.
    - iIntros "IC"; iLeft; iFrame; eauto.
    - eapply simF_fire.
  Qed.
End CannonIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Lemma ctxr (sp : specmap) :
    ctx_refines (CannonI.t, emp%I) (CannonA.t sp, CannonA.Ready).
  Proof using. eapply main_adequacy, sim. Qed.
End ctxr. End CannonIA.
