Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.
Require Import CannonMainI CannonMainA.

Module CannonMainIA. Section CannonMainIA.
  Import CannonA CannonMainA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !cannonGS}.

  Context (sp : specmap).
  Context (CannonInMain : CannonA.sp ⊆ sp).

  Definition Ist : ist_type Σ := λ _ _, True%I.

  Local Notation MainAMod := (MainA.t 1 sp).
  Local Notation MainIMod := (MainI.t 1).
  
  Lemma simF_main : ISim.sim_fun open MainAMod MainIMod Ist None.
  Proof using CannonInMain.
    iStartSim.

    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "[-> B]". destruct Any.downcast; steps_l; ss. simpl_sp.

    (* SRC: prove the precondition of "fire" *)
    steps_r. force_l. instantiate (1:=()). force_l.
    force_l. iFrame; iSplit; eauto. steps_l.

    (* SRC, TGT; call "fire" and take a postcondition *)
    call "IST"; eauto. clear dependent st_src st_tgt. iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[% %]"; des; subst. hss.
    steps_r. hss. steps_r.
    
    (* SRC, TGT: print 1 *)
    step. steps_l. steps_r.

    (* SRC: prove the postcondition & IST *)
    forces_l. iSplit; eauto.
    step. iFrame; et.
  (*SLOW*)Qed.

  Theorem sim : ISim.t open MainAMod MainIMod emp%I Ist.
  Proof using CannonInMain.
    init_sim.
    { iIntros "_"; done. }
    { eapply simF_main. }
  Qed.
End CannonMainIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !cannonGS}.

  Theorem ctxr (sp : specmap) :
    CannonA.sp ⊆ sp →
    ctx_refines
      (MainA.t 1 sp, emp%I)
      (MainI.t 1,    emp%I).
  Proof. i; eapply main_adequacy, sim; eauto. Qed.
End ctxr. End CannonMainIA.
