Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.
Require Import CannonMainI CannonMainA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CannonMainIA. Section CannonMainIA.
  Import CannonAS.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{!cannonG}.

  Context (SpMain : sp_type).
  Context (CannonInMain : sp_incl CannonAS.Sp SpMain).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MainAMod := (MainA.t 1 SpMain).
  Local Definition MainIMod := (MainI.t 1).
  
  Lemma simF_main : HSim.sim_fun open MainAMod MainIMod MainA.init_cond Ist None.
  Proof using SpMain CannonInMain.
    init_simF.

    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((%Y & B) & %Q)". subst. hss.

    (* SRC: prove the precondition of "fire" *)
    steps_r. force_l. instantiate (1:=()). force_l.
    force_l. iSplitL "B"; et. steps_l.

    (* SRC, TGT; call "fire" and take a postcondition *)
    call "IST"; et. steps_l. iDestruct "ASM" as "[% %]"; des; subst. hss.
    steps_r. hss. steps_r.
    
    (* SRC, TGT: print 1 *)
    step. steps_l. steps_r. force_l.

    (* SRC: prove the postcondition & IST *)
    force_l. iSplitR; et. steps_l.
    step. iFrame; et.
  (*SLOW*)Qed.

  Theorem sim : HSim.t open MainAMod MainIMod MainA.init_cond Ist.
  Proof using SpMain CannonInMain.
    init_sim.
    - exfalso. rewrite /MainI.t in H1. revert H1. unseal CRIS. i; ss.
    - eapply simF_main.
  Qed.
End CannonMainIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{!cannonG}.

  Theorem ctxr (SpMain : string → option fspec)
    (CannonInMain : sp_incl CannonAS.Sp SpMain)
  :
    ctx_refines
      (MainA.t 1 SpMain, (MainA.init_cond))
      (MainI.t 1, (emp%I)).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End CannonMainIA.
