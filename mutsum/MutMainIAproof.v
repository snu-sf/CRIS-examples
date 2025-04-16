Require Import CRIS.

Require Import MutFA MutGA.
Require Import MutHeader MutMainHeader MutMainI MutMainA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module MutMainIA. Section MutMainIA.
  Import MutAUX.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Context (Sp SpPure: string -> option fspec).
  Context (APCInSp : sp_incl (APCA.Sp) Sp).
  Context (FInPure : sp_incl (MutFA.SpF) SpPure).
  Context (PureInSp : sp_sub SpPure Sp).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MutMainAMod := ((MutMainA.t Sp) ★ APCA.t SpPure Sp).
  Local Definition MutMainIMod := ((MutMainI.t) ★ APCA.t SpPure Sp).
  Local Definition IstFull := (IstProd (IstSB (MutMainA.t Sp).(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_main:
    HSim.sim_fun open MutMainAMod MutMainIMod IstFull MutMainHdr.main.
  Proof using _sinvG APCInSp FInPure PureInSp.
    init_simF.

    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "%". des; subst; hss.

    (* SRC: handle pure (APC) *)
    rewrite /pure.
    force_l 11. steps_l. forces_l. iSplitR; eauto.
    steps_l.
    
    (* SRC: inlining APC *)
    inline_l. steps_l. iDestruct "ASM" as "[-> <-]"; hss.
    steps_l. rewrite /APC. force_l 1. steps_l.

    (* SRC, TGT: call mutg using APC tactic *)
    steps_r. apc_call "IST"; eauto.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). eapply OrdArith.lt_from_nat. nia. }
    { eapply FInPure. rewrite /MutFA.SpF. unseal CRIS. ss. }
    { instantiate (1:=10). iSplitR; eauto. iPureIntro. esplits; eauto; [unfold mut_max; nia|refl]. }
    iDestruct "ISTPOST" as "[IST ->]".
    
    (* SRC: jump APC *)
    apc_l. steps_l. steps_r. hss. steps_r.
    forces_l. iSplitR; first done.
    steps_l. forces_l. steps_l. forces_l. iSplitR; eauto.

    (* SRC, TGT: prove the IST *)
    step. iSplitR "IST"; eauto.
    Unshelve. all: ss.
  (*SLOW*)Qed.

  Theorem sim:
    HSim.t open MutMainAMod MutMainIMod MutMainA.init_cond IstFull.
  Proof.
    init_sim.
    - iIntros "IC". iExists [], [], [], []. iSplitR; et.
      iSplit; et. iSplit; et. iPureIntro. esplits; ss.
    - apply simF_main; eauto.
  Qed.
End MutMainIA.

Section ctxr.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Theorem ctxr (Sp SpPure: string → option fspec)
    (APCInSp : sp_incl (APCA.Sp) Sp)
    (FInPure : sp_incl (MutFA.SpF) SpPure)
    (PureInSp : sp_sub SpPure Sp)
  :
    ctx_refines
      (MutMainA.t Sp ★ APCA.t SpPure Sp, emp%I)
      (MutMainI.t ★ APCA.t SpPure Sp, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MutMainIA.
