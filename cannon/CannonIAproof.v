Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.

Set Implicit Arguments.
Local Open Scope nat_scope.

Module CannonIA. Section CannonIA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Context (Spc_s : string → option fspec).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_s st_t,
      (⌜st_s = [(CannonA.v_lv, 1%Z↑)] /\ st_t = [(CannonI.v_lv, 1%Z↑)]⌝ ∗ Ready)
      ∨ Fired
    )%I.
  
  Local Definition CannonAMod := (CannonA.t Spc_s).
  Local Definition CannonIMod := (CannonI.t).

  Lemma simF_fire : HSim.sim_fun open CannonAMod CannonIMod Ist CannonName.fire.
  Proof.
    init_simF 0 0.

    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((%Y & B) & %Q)". subst. hss.
    unfold Ist. iDestruct "IST" as "[[% R] | F]"; des; subst; cycle 1. 
    (* already fired *)
    { iExFalso. iApply FiredBall. iFrame. }

    steps_r. hss. steps_r.
    change (1 `div` 1)%Z with 1%Z.
    
    (* SRC, TGT: print 1 *)
    step. steps_r.

    (* prove postcondition & the IST - Ready * Ball = Shot *)
    rewrite /alist_upd /_alist_upd /=. replace (1 - 1)%Z with 0%Z by nia.
    steps_l. forces_l. iSplitR; eauto. step.
    iSplit; eauto. iRight. iApply ReadyBall; iFrame.
  (*FAST*)Qed.

  Theorem sim : HSim.t open CannonAMod CannonIMod CannonA.init_cond Ist.
  Proof.
    init_sim.
    - iIntros "IC". unfold Ist, CannonA.init_cond. iLeft. iFrame; eauto.
    - eapply simF_fire.
  Qed.
End CannonIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!CannonAGΓ Γ}.

  Theorem ctxr (Spc_s : string → option fspec):
    ctx_refines
      (CannonA.t Spc_s, CannonA.init_cond)
      (CannonI.t, emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End ctxr. End CannonIA.
