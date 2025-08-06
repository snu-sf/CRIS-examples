Require Import CRIS.
Require Import MutHeader MutGI MutGA MutFA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module MutGIA. Section MutGIA.
  Import MutAUX.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Context (Sp: sp_type).
  Context (SpPure: spl_type).

  Context (APCInSp : sp_incl APCA.Sp Sp).
  Context (FInPure : spl_sub MutFA.SpF SpPure).
  Context (PureInSp : sp_incl SpPure Sp).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MutGAMod := (MutGA.t Sp ★ APCA.t SpPure Sp).
  Local Definition MutGIMod := (MutGI.t ★ APCA.t SpPure Sp).
  Local Definition IstFull := (IstProd (IstSB (MutGA.t Sp).(Mod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_mutg:
    ISim.sim_fun open MutGAMod MutGIMod MutGA.init_cond IstFull (Some MutHdr.mutg).
  Proof using _crisG APCInSp FInPure PureInSp.
    init_simF.
    
    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; hss.

    (* TGT: take steps *)
    steps_r. unfold assume. force_r. steps_r.
    
    (* destruct cases of the number of recursive call *)
    destruct _q; s.
    { (* f(0) *)
      steps_r. steps_l. forces_l. iSplitR; et. steps_l.

      (* SRC: inlining APC *)
      inline_l. steps_l. iDestruct "ASM" as "[-> <-]"; hss. steps_l.
      rewrite /APC. force_l _q. steps_l.
      
      (* SRC: jump APC *)
      apc_l. steps_l. forces_l. iSplitR; eauto. steps_l.
      forces_l. iSplitR; eauto.

      (* SRC, TGT : prove the IST *)
      step. iSplitR "IST"; iFrame; auto.
    }

    (* f(S n) *)
    replace (S _q - 1)%Z with (Z.of_nat _q) by nia.
    steps_l. force_l vo. steps_l. forces_l. iSplitR; eauto.

    (* SRC: inlining APC in order to call mutg *)
    inline_l. steps_l. iDestruct "ASM" as "[-> <-]"; hss. steps_l.
    rewrite /APC. force_l 1. steps_l.

    (* SRC, TGT : call mutg using APC tactic *)
    steps_r. apc_call "IST"; eauto.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=_q). eapply Ord.lt_le_lt; eauto. eapply OrdArith.lt_from_nat. nia. }
    { apply FInPure. unfold MutFA.SpF. unseal CRIS. ss. }
    { iFrame. iPureIntro. esplits; eauto; [nia|refl]. }
    iDestruct "ISTPOST" as "[IST ->]".

    (* SRC: jump APC *)
    apc_l. steps_r. hss. steps_r. steps_l.
    forces_l; iSplitR; eauto. steps_l.
    forces_l; iSplitR; eauto. steps_l.
    step. iSplitR "IST"; iFrame; eauto.
    { iPureIntro; do 2 f_equal; nia. }

    (* prove shelved goals *)
    Unshelve. all: ss.
    { eapply mut_max_intrange; eauto. }
    { exact (0↑). }
  (*SLOW*)Admitted.

  Theorem sim:
    ISim.t open MutGAMod MutGIMod MutGA.init_cond IstFull.
  Proof.
    init_sim.
    - splits; eauto. iIntros "C". iFrame. iPureIntro.
      rewrite /MutGA.scopes /state_scopes /incl //.
    - eapply simF_mutg.
  Qed.
End MutGIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Theorem ctxr (Sp : sp_type) (SpPure: spl_type) 
    (APCInSp : sp_incl APCA.Sp Sp)
    (FInPure : spl_sub MutFA.SpF SpPure)
    (PureInSp : sp_incl SpPure Sp)
  :
    ctx_refines
      (MutGA.t Sp ★ APCA.t SpPure Sp, MutGA.init_cond)
      (MutGI.t ★ APCA.t SpPure Sp, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MutGIA.
