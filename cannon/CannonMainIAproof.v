Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.
Require Import CannonMainI CannonMainA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CannonMainIA. Section CannonMainIA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!CannonAGΓ Γ}.

  Context (SpcMain : string → option fspec).
  Context (CannonInMain : spc_incl CannonAS.Spc SpcMain).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MainAMod := (MainA.t 1 SpcMain).
  Local Definition MainIMod := (MainI.t 1).
  
  Lemma simF_main : HSim.sim_fun open MainAMod MainIMod Ist MainHdr.main.
  Proof.
    init_simF 0 0.

    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((%Y & B) & %Q)". subst. hss.

    (* SRC: prove the precondition of "fire" *)
    steps_r. unfold HoareCall. force_l. instantiate (1:=()). force_l.
    force_l. iSplitL "B"; et. steps_l.

    (* SRC, TGT; call "fire" and take a postcondition *)
    call "IST"; et. steps_l. iDestruct "ASM" as "[% %]"; des; subst. hss.
    steps_r. hss. steps_r.
    
    (* SRC, TGT: print 1 *)
    step. steps_l. steps_r. force_l.

    (* SRC: prove the postcondition & IST *)
    force_l. iSplitR; et. steps_l.
    step. iFrame; et.
  (*FAST*)Qed.

  Theorem sim : HSim.t open MainAMod MainIMod MainA.init_cond Ist.
  Proof.
    init_sim.
    - iIntros "IC". et.
    - apply simF_main; eauto.
  Qed.
End CannonMainIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!CannonAGΓ Γ}.

  Theorem ctxr (SpcMain : string → option fspec)
    (CannonInMain : spc_incl CannonAS.Spc SpcMain)
  :
    ctx_refines
      (MainA.t 1 SpcMain, (MainA.init_cond))
      (MainI.t 1, (emp%I)).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End CannonMainIA.
