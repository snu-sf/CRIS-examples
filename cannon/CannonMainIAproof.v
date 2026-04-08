Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.
Require Import CannonMainI CannonMainA.

Module CannonMainIA. Section CannonMainIA.
  Import CannonA CannonMainA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Context (sp : specmap).
  Context (CannonInMain : CannonA.sp ⊆ sp).

  Definition Ist : ist_type Σ := λ _ _, True%I.

  Local Notation MainAMod := (MainA.t 1 sp).
  Local Notation MainIMod := (MainI.t 1).
  
  Lemma simF_main : ISim.sim_fun open MainAMod MainIMod Ist entry.
  Proof using CannonInMain.
    cStartFunSim.

    (* SRC: precondition *)
    cStepsS. iDestruct "ASM" as "[-> B]". destruct Any.downcast; cStepsS; ss. simpl_sp.

    (* SRC: prove the precondition of "fire" *)
    cStepsT. cForceS (). cForcesS. iFrame; iSplit; eauto.

    (* SRC, TGT; cCall "fire" and take a postcondition *)
    cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsS. iDestruct "ASM" as "[% %]"; des; subst. cSimpl.
    cStepsT. cStepsS.
    
    (* SRC, TGT: print 1 *)
    cStep.

    (* SRC: prove the postcondition & IST *)
    cForcesS. iSplit; eauto.
    cStep. iFrame; et.
  (*SLOW*)Qed.

  Theorem sim : ISim.t open MainAMod MainIMod emp%I Ist.
  Proof using CannonInMain.
    cStartModSim.
    { iIntros "_"; done. }
    { eapply simF_main. }
  Qed.
End CannonMainIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Theorem ctxr (sp : specmap) :
    CannonA.sp ⊆ sp →
    ctx_refines
      (MainI.t 1,    emp%I)
      (MainA.t 1 sp, emp%I).
  Proof. i; eapply main_adequacy, sim; eauto. Qed.
End ctxr. End CannonMainIA.
