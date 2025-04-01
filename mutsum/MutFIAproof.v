Require Import CRIS.

Require Import NormITree.
Require Import MutHeader MutFI MutFA MutGA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module MutFIA. Section MutFIA.
  Import MutAUX.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Context (u_s u_apc: univ_id).
  Context (Sp: string -> option fspec).
  Context (SpPure: string -> option fspec).

  Context (APCInSp : sp_incl (APCA.Sp) Sp).
  Context (GInPure : sp_incl (MutGA.SpG) SpPure).
  Context (PureInSp : sp_sub SpPure Sp).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MutFAMod := (MutFA.t u_s Sp ★ APCA.t u_apc SpPure Sp).
  Local Definition MutFIMod := (MutFI.t ★ APCA.t u_apc SpPure Sp).
  Local Definition IstFull := (IstProd (IstSB (MutFA.t u_s Sp).(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_mutf:
    HSim.sim_fun open MutFAMod MutFIMod IstFull MutHdr.mutf.
  Proof.
    init_simF u_s 0.

    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; hss.

    (* TGT: take steps *)
    steps_r. unfold assume. force_r. steps_r.
    
    (* destruct cases of the number of recursive call *)
    destruct q; s.
    { (* f(0) *)
      steps_r. force_l. steps_l.
      forces_l. iSplitR; et. steps_l. 

      (* SRC: inlining APC *)
      inline_l. steps_l. iDestruct "ASM" as "[-> <-]"; hss. steps_l.
      rewrite /APC. force_l q. steps_l.
      
      (* SRC: jump APC *)
      apc_l. steps_l. forces_l. iSplitR; eauto. steps_l.
      forces_l. iSplitR; eauto.

      (* SRC, TGT : prove the IST *)
      step. iSplitR "IST"; iFrame; auto.
    }

    (* f(S n) *)
    replace (S q - 1)%Z with (Z.of_nat q) by nia.
    steps_l. force_l vo. steps_l. forces_l. iSplitR; eauto.

    (* SRC: inlining APC in order to call mutg *)
    inline_l. steps_l. iDestruct "ASM" as "[-> <-]"; hss. steps_l.
    rewrite /APC. force_l 1. steps_l.

    (* SRC, TGT : call mutg using APC tactic *)
    steps_r. apc_call "IST"; eauto.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=q). eapply Ord.lt_le_lt; eauto. eapply OrdArith.lt_from_nat. nia. }
    { apply GInPure. unfold MutGA.SpG. unseal CRIS. ss. }
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
  (*FAST*)Qed.

  Theorem sim:
    HSim.t open MutFAMod MutFIMod MutFA.init_cond IstFull.
  Proof.
    init_sim.
    - iIntros "C". iExists [], [], [], []. do 2 iSplit; eauto. iFrame. iPureIntro.
      rewrite /MutFA.scopes /state_scopes /incl //.
    - eapply simF_mutf.
  Qed.
End MutFIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Theorem ctxr (u_s u_apc: univ_id) (Sp SpPure: string → option fspec) 
    (APCInSp : sp_incl (APCA.Sp) Sp)
    (GInPure : sp_incl (MutGA.SpG) SpPure)
    (PureInSp : sp_sub SpPure Sp)
  :
    ctx_refines
      (MutFA.t u_s Sp ★ APCA.t u_apc SpPure Sp, MutFA.init_cond)
      (MutFI.t ★ APCA.t u_apc SpPure Sp, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MutFIA.
