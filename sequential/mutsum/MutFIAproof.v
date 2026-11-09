From CRIS.common Require Import CRIS.
From CRIS.mutsum Require Import MutHeader MutFI MutFA MutGA.
From CRIS.apc Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module MutFIA. Section MutFIA.
  Import MutAUX.
  Context `{_crisG: !crisG Γ Σ α β τ Hinv Hsub}.

  Context (Sp SpPure: specmap).

  Context (APCInSp : APCA.sp ⊆ Sp).
  Context (GInPure : MutGA.SpG ⊆ SpPure).
  Context (PureInSp : SpPure ⊆ Sp).

  Section SIM_FUNS.

    Context `{STATE : !stateGS Σ}.

    Definition Ist : iProp Σ := True%I.

    Local Definition MutFAMod := (MutFA.t Sp ★ APCA.t SpPure Sp).
    Local Definition MutFIMod := (MutFI.t ★ APCA.t SpPure Sp).
    Local Notation IstFull :=
      (Ist ∗ IstEq (APCA.t SpPure Sp))%I.

    (*************)

    Lemma simF_mutf:
      ⊢ ISim.sim_fun open MutFAMod MutFIMod IstFull (fid MutHdr.mutf).
    Proof using _crisG APCInSp GInPure PureInSp.
      cStartFunSim. rewrite /MutFI.fF.

      (* SRC: precondition *)
      cStepsS. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; cSimpl.

      (* TGT: take cSteps *)
      cStepsT. unfold assume. cForceT.

      (* destruct cases of the number of recursive cCall *)
      destruct _q; s.
      { (* f(0) *)
        rewrite /pure_body /cfunN.
        iSplit; first (iPureIntro; eapply mut_max_intrange; eauto).
        cStepsS. cSimpl.
        cForcesS. iSplitR; et. cStepsS.

        (* SRC: inlining APC *)
        cInlineS. cStepsS. iDestruct "ASM" as "[-> <-]"; cSimpl. cStepsS.
        rewrite /APCA.apc_body /APC. cForceS _q. cStepsS.

        (* SRC: jump APC *)
        apcS. cStepsS. cForcesS. iSplitR; eauto. cStepsS.
        cForcesS. iSplitR; eauto.

        (* SRC, TGT : prove the IST *)
        cStep. iSplitR "IST"; iFrame; auto.
      }

      (* f(S n) *)
      replace (S _q - 1)%Z with (Z.of_nat _q) by nia.
      rewrite /pure_body /cfunN.
      iSplit; first (iPureIntro; eapply mut_max_intrange; eauto).
      cStepsS. cSimpl.
      cForceS vo. cStepsS. cForcesS. iSplitR; eauto.

      (* SRC: inlining APC in order to cCall mutg *)
      cInlineS. cStepsS. iDestruct "ASM" as "[-> <-]"; cSimpl. cStepsS.
      rewrite /APCA.apc_body /APC. cForceS 1. cStepsS.

      (* SRC, TGT : cCall mutg using APC tactic *)
      cStepsT. apcCall/ "IST" as (?) "ISTPOST"; eauto.
      { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
      { instantiate (1:=_q). eapply Ord.lt_le_lt; eauto. eapply OrdArith.lt_from_nat. nia. }
      { iFrame. iPureIntro. esplits; eauto; [nia|refl]. }
      iDestruct "ISTPOST" as "[IST ->]".

      (* SRC: jump APC *)
      apcS. cStepsT. cStepsT. cStepsS.
      cForcesS; iSplitR; eauto. cStepsS.
      cForcesS; iSplitR; eauto. cStepsS.
      cStep. iSplitR "IST"; iFrame; eauto.
      { iPureIntro; do 2 f_equal; nia. }

      (* prove shelved goals *)
      Unshelve. all: ss.
      { exact (0↑). }
      { exact (0↑). }
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim:
    MutFA.init_cond ⊢ ISim.t open MutFAMod MutFIMod.
  Proof.
    iIntros "C".
    iApply (ISim_reflR open (MutFA.t Sp) MutFI.t
      (APCA.t SpPure Sp) (fun _ : stateGS Σ => Ist) with "[C] []").
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT". done.
    - iIntros (STATE). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split; mod_tac. }
      iIntros (fn) "%Hfn".
      repeat rewrite Mod.dom_fnsems_add in Hfn.
      set_unfold in Hfn; des; subst.
      iApply simF_mutf.
  Qed.
End MutFIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ctxr (Sp SpPure : specmap)
    (APCInSp : APCA.sp ⊆ Sp)
    (GInPure : MutGA.SpG ⊆ SpPure)
    (PureInSp : SpPure ⊆ Sp) :
    MutFA.init_cond ⊢
      ctx_refines (MutFI.t ★ APCA.t SpPure Sp) (MutFA.t Sp ★ APCA.t SpPure Sp).
  Proof.
    etrans; first (eapply sim; eauto).
    eapply main_adequacy.
  Qed.
End ctxr. End MutFIA.
