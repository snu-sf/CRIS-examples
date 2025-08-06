Require Import CRIS.

Require Import MutFA MutGA.
Require Import MutHeader MutMainI MutMainA.
Require Import APCHeader APC APCA APCC APCTactics.

Set Implicit Arguments.

Module MutMainIA. Section MutMainIA.
  Import MutAUX.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Context (Sp : sp_type).
  Context (SpPure: spl_type).
  Context (APCInSp : sp_incl APCA.Sp Sp).
  Context (FInPure : spl_sub MutFA.SpF SpPure).
  Context (PureInSp : sp_incl SpPure Sp).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MutMainAMod := ((MutMainA.t true Sp) ★ APCA.t SpPure Sp).
  Local Definition MutMainIMod := ((MutMainI.t) ★ APCA.t SpPure Sp).
  Local Definition IstFull := (IstProd (IstSB (MutMainA.t true Sp).(Mod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_main:
    ISim.sim_fun open MutMainAMod MutMainIMod MutMainA.init_cond IstFull None.
  Proof using _crisG APCInSp FInPure PureInSp.
    init_simF.

    (* SRC: precondition *)
    steps_l. iDestruct "IST" as "%"; des; hss.

    (* SRC: handle pure (APC) *)
    rewrite /pure.
    force_l 11. steps_l. forces_l. iSplitR; eauto.
    steps_l.
    
    (* SRC: inlining APC *)
    inline_l. steps_l. iDestruct "ASM" as "[-> <-]"; hss.
    steps_l. rewrite /APC. force_l 1. steps_l.

    (* SRC, TGT: call mutg using APC tactic *)
    steps_r. apc_call ""; eauto.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). eapply OrdArith.lt_from_nat. nia. }
    { eapply FInPure. rewrite /MutFA.SpF. unseal CRIS. ss. }
    { instantiate (1:=10). iSplit; eauto. 
      { iPureIntro. esplits; eauto; [unfold mut_max; nia|refl]. }
      { do 4 iExists _. iSplit; iPureIntro; esplits; eauto; unfold_mod; ss. }
    }
    iDestruct "ISTPOST" as "[IST ->]".
    
    (* SRC: jump APC *)
    apc_l. steps_l. steps_r. hss. steps_r.
    forces_l. iSplitR; first done.
    steps_l. forces_l.

    (* SRC, TGT: prove the IST *)
    step. iSplitR "IST"; eauto.
    Unshelve. all: ss.
  (*SLOW*)Admitted.

  Theorem sim:
    ISim.t open MutMainAMod MutMainIMod MutMainA.init_cond IstFull.
  Proof.
    init_sim.
    (* - inv H. *)
    - apply simF_main; eauto.
  Qed.

  Theorem ctxr:
    ctx_refines
      (MutMainA.t true Sp ★ APCA.t SpPure Sp, emp%I)
      (MutMainI.t ★ APCA.t SpPure Sp, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.

  Theorem ctxr_close:
    ctx_refines
      (MutMainA.t false Sp ★ APCC.t Sp, emp%I)
      (MutMainA.t true  Sp ★ APCC.t Sp, emp%I).
  Proof using _crisG APCInSp FInPure PureInSp.
    eapply main_adequacy
      with (Ist := IstProd (IstSB MutMainA.scopes IstEq) IstEq).
    init_sim.
    (* { inv H. } *)
    { init_simF.
      steps_l. forces_r.
      iDestruct "IST" as "%"; des; hss.
      rewrite /pure. steps_r. inline_r. forces_r.
      iDestruct "GRT" as "(% & %)". subst. iSplitR; et.
      hss. steps_r. forces_r. iSplitR; et.
      steps_r. forces_l. step. eauto.
    }
  Unshelve. all: et.
  Qed.

End MutMainIA. End MutMainIA.
