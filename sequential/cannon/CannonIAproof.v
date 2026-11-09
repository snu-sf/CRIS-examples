From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.cannon Require Import CannonHeader CannonI CannonA.

Module CannonIA. Section CannonIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.
  Import CannonA.

  Context (sp : specmap).

  Section SIM_FUNS.

    Context `{STATE : !stateGS Σ}.

    Definition Ist : iProp Σ :=
      ((CannonI.v_lv ↦tgt 1%Z↑ ∗ Ready) ∨
       (CannonI.v_lv ↦tgt 0%Z↑ ∗ Fired))%I.

    Local Definition CannonAMod := (CannonA.t sp).
    Local Definition CannonIMod := (CannonI.t).

    Lemma simF_fire :
      ⊢ ISim.sim_fun open CannonAMod CannonIMod Ist (fid CannonHdr.fire).
    Proof using.
      cStartFunSim. rewrite /CannonI.fire /fire.

      (* SRC: precondition *)
      cStepsS. iDestruct "ASM" as "[-> [% [-> [-> B]]]]". cSimpl.
      iDestruct "IST" as "[[LV R] | [LV F]]"; cycle 1.
      (* already fired *)
      { iExFalso. iApply FiredBall; iFrame. }

      cStepsS. cStepsT.
      change (1 `div` 1)%Z with 1%Z.

      (* SRC, TGT: print 1 *)
      cStep. cStepsT.

      (* prove postcondition & the IST - Ready * Ball = Shot *)
      cStepsS. cForcesS. iSplitR; eauto. cStep.
      iSplit; eauto. iRight. iFrame. iApply ReadyBall; iFrame.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim : CannonA.Ready ⊢ ISim.t open CannonAMod CannonIMod.
  Proof using.
    cStartModSim (fun STATE : stateGS Σ => Ist (STATE := STATE)).
    - iPoseProof (state_init_tgt_acc _ _ CannonI.v_lv with "TGT") as
        (ov) "(%Hlv & LV & _)".
      { set_solver. }
      simpl_map. subst ov. iLeft. iFrame.
    - iApply simF_fire.
  Qed.
End CannonIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Lemma ctxr (sp : specmap) :
    CannonA.Ready ⊢ ctx_refines CannonI.t (CannonA.t sp).
  Proof using.
    etrans; first eapply sim.
    eapply main_adequacy.
  Qed.
End ctxr. End CannonIA.
