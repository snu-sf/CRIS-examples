From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.cannon Require Import CannonHeader CannonI CannonA.
From CRIS.cannon Require Import CannonMainI CannonMainA.

Module CannonMainIA. Section CannonMainIA.
  Import CannonA CannonMainA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Context (sp : specmap).
  Context (CannonInMain : CannonA.sp ⊆ sp).

  Local Notation MainAMod := (MainA.t 1 sp).
  Local Notation MainIMod := (MainI.t 1).

  Section SIM_FUNS.

    Context `{STATE : !stateGS Σ}.

    Definition Ist : iProp Σ := True%I.


    Lemma simF_main :
      ⊢ ISim.sim_fun open MainAMod MainIMod Ist entry.
    Proof using CannonInMain.
      cStartFunSim. rewrite /MainA.main /MainI.main.

      (* SRC: precondition *)
      cStepsS. iDestruct "ASM" as "[-> B]". cSimpl.

      (* SRC: prove the precondition of "fire" *)
      cStepsT. cForceS (). cForcesS. iFrame; iSplit; eauto.

      (* SRC, TGT; cCall "fire" and take a postcondition *)
      cCall "IST" as (ret) "IST".
      cStepsS. iDestruct "ASM" as "[% %]"; des; subst. cSimpl.
      cStepsT. cStepsS.

      (* SRC, TGT: print 1 *)
      cStep.

      (* SRC: prove the postcondition & IST *)
      cForcesS. iSplit; eauto.
      cStep. iFrame; et.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Theorem sim : ⊢ ISim.t open MainAMod MainIMod.
  Proof using CannonInMain.
    cStartModSim (fun _ : stateGS Σ => Ist).
    - done.
    - iApply simF_main.
  Qed.
End CannonMainIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Theorem ctxr (sp : specmap) :
    CannonA.sp ⊆ sp →
    ⊢ ctx_refines (MainI.t 1) (MainA.t 1 sp).
  Proof.
    intros.
    iApply main_adequacy.
    iApply sim; eauto.
  Qed.
End ctxr. End CannonMainIA.
