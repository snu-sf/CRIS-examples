Require Import CRIS.
Require Import MutHeader MutFI MutFA MutGA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module MutFIA. Section MutFIA.
  Import MutAUX.
  Context `{_crisG: !crisG Γ Σ α β τ Hinv Hsub}.

  Context (Sp SpPure: specmap).

  Context (APCInSp : APCA.sp ⊆ Sp).
  Context (GInPure : MutGA.SpG ⊆ SpPure).
  Context (PureInSp : SpPure ⊆ Sp).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    (λ _ _, True)%I.

  Local Definition MutFAMod := (MutFA.t Sp ★ APCA.t SpPure Sp).
  Local Definition MutFIMod := (MutFI.t ★ APCA.t SpPure Sp).
  Local Definition IstFull := (IstProd (IstSB (MutFA.t Sp).(Mod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_mutf:
    ISim.sim_fun open MutFAMod MutFIMod IstFull (fid MutHdr.mutf).
  Proof using _crisG APCInSp GInPure PureInSp.
    cStartFunSim. rewrite /MutFI.fF.

    (* SRC: precondition *)
    cStepsS. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; cSimpl.

    (* TGT: take cSteps *)
    cStepsT. unfold assume. cForceT. cStepsT.
    
    (* destruct cases of the number of recursive cCall *)
    destruct _q; s.
    { (* f(0) *)
      rewrite /pure_body /cfunN.
      cStepsT. cStepsS. cSimpl.
      cForcesS. iSplitR; et. cStepsS. 

      (* SRC: inlining APC *)
      cInlineS. cStepsS. iDestruct "ASM" as "[-> <-]"; cSimpl. cStepsS.
      rewrite /APC. cForceS _q. cStepsS.
      
      (* SRC: jump APC *)
      apcS. cStepsS. cForcesS. iSplitR; eauto. cStepsS.
      cForcesS. iSplitR; eauto.

      (* SRC, TGT : prove the IST *)
      cStep. iSplitR "IST"; iFrame; auto.
    }

    (* f(S n) *)
    replace (S _q - 1)%Z with (Z.of_nat _q) by nia.
    rewrite /pure_body /cfunN. cStepsS. cSimpl.
    cForceS vo. cStepsS. cForcesS. iSplitR; eauto.

    (* SRC: inlining APC in order to cCall mutg *)
    cInlineS. cStepsS. iDestruct "ASM" as "[-> <-]"; cSimpl. cStepsS.
    rewrite /APC. cForceS 1. cStepsS.

    (* SRC, TGT : cCall mutg using APC tactic *)
    cStepsT. apcCall "IST" as (???) "ISTPOST"; eauto.
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
    { eapply mut_max_intrange; eauto. }
    { exact (0↑). }
    { exact (0↑). }
  (*SLOW*)Qed.

  Lemma sim:
    ISim.t open MutFAMod MutFIMod MutFA.init_cond IstFull.
  Proof.
    cStartModSim.
    - eapply simF_mutf.
    - iIntros "C". iFrame. do 4 iExists _. iPureIntro; esplits; eauto; set_solver.
  Qed.
End MutFIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ctxr (Sp SpPure : specmap)
    (APCInSp : APCA.sp ⊆ Sp)
    (GInPure : MutGA.SpG ⊆ SpPure)
    (PureInSp : SpPure ⊆ Sp) :
    ctx_refines
      (MutFI.t ★ APCA.t SpPure Sp, emp%I)
      (MutFA.t Sp ★ APCA.t SpPure Sp, MutFA.init_cond).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MutFIA.
