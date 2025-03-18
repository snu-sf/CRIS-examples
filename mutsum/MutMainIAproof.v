Require Import CRIS.

Require Import MutFA MutGA.
Require Import MutHeader MutMainHeader MutMainI MutMainA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module MutMainIA. Section MutMainIA.
  Import MutAUX.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Context (u_s u_apc: univ_id).
  Context (Spc SpcPure: string -> option fspec).
  Context (APCInSpc : spc_incl (APCA.Spc) Spc).
  Context (FInPure : spc_incl (MutFA.SpcF) SpcPure).
  Context (PureInSpc : spc_sub SpcPure Spc).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp :=
    λ _ _ _, (True)%I.

  Local Definition MutMainAMod := ((MutMainA.t u_s Spc) ★ APCA.t u_apc SpcPure Spc).
  Local Definition MutMainIMod := ((MutMainI.t) ★ APCA.t u_apc SpcPure Spc).
  Local Definition IstFull := (IstProd (IstSB (MutMainA.t u_s Spc).(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_main:
    HSim.sim_fun open MutMainAMod MutMainIMod IstFull MutMainName.main.
  Proof.
    init_simF u_s 0.

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
    { eapply FInPure. rewrite /MutFA.SpcF. unseal CRIS. ss. }
    { instantiate (1:=10). iSplitR; eauto. iPureIntro. esplits; eauto; [unfold mut_max; nia|refl]. }
    iDestruct "ISTPOST" as "[IST ->]".
    
    (* SRC: jump APC *)
    apc_l. steps_l. steps_r. hss. steps_r.
    forces_l. iSplitR; first done.
    steps_l. forces_l. steps_l. forces_l. iSplitR; eauto.

    (* SRC, TGT: prove the IST *)
    step. iSplitR "IST"; eauto.
    Unshelve. all: ss.
  (*FAST*)Qed.

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
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Theorem ctxr (u_s u_apc: univ_id) (Spc SpcPure: string → option fspec)
    (APCInSpc : spc_incl (APCA.Spc) Spc)
    (FInPure : spc_incl (MutFA.SpcF) SpcPure)
    (PureInSpc : spc_sub SpcPure Spc)
  :
    ctx_refines
      (MutMainA.t u_s Spc ★ APCA.t u_apc SpcPure Spc, emp%I)
      (MutMainI.t ★ APCA.t u_apc SpcPure Spc, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MutMainIA.
