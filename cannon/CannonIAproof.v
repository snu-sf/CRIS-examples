Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.

Set Implicit Arguments.
Local Open Scope nat_scope.

Module CannonIA. Section CannonIA.
  Import CannonAS.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!cannonG}.

  Context (Sp_s : sp_type).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_s st_t,
      (⌜st_s = [(CannonA.v_lv, 1%Z↑)] /\ st_t = [(CannonI.v_lv, 1%Z↑)]⌝ ∗ Ready)
      ∨ Fired
    )%I.
  
  Local Definition CannonAMod := (CannonA.t Sp_s).
  Local Definition CannonIMod := (CannonI.t).

  Lemma simF_fire : ISim.sim_fun open CannonAMod CannonIMod CannonA.init_cond Ist (Some CannonHdr.fire).
  Proof using.
    init_simF.

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
  (*SLOW*)Admitted.

  Theorem sim : ISim.t open CannonAMod CannonIMod CannonA.init_cond Ist.
  Proof using.
    init_sim.
    - split; eauto. iIntros "IC". unfold Ist, CannonA.init_cond. iLeft. iFrame; eauto.
    - eapply simF_fire.
  Qed.
End CannonIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!cannonG}.

  Theorem ctxr (Sp_s : string → option fspec):
    ctx_refines
      (CannonA.t Sp_s, CannonA.init_cond)
      (CannonI.t, emp%I).
  Proof using. eapply main_adequacy, sim. Qed.
End ctxr. End CannonIA.
