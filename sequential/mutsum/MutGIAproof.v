From CRIS.common Require Import CRIS.
From CRIS.mutsum Require Import MutHeader MutGI MutGA MutFA.
From CRIS.apc Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module MutGIA. Section MutGIA.
  Import MutAUX.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Context (Sp SpPure: specmap).

  Context (APCInSp : APCA.sp ⊆ Sp).
  Context (FInPure : MutFA.SpF ⊆ SpPure).
  Context (PureInSp : SpPure ⊆ Sp).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    (λ _ _, True)%I.

  Local Definition MutGAMod := (MutGA.t Sp ★ APCA.t SpPure Sp).
  Local Definition MutGIMod := (MutGI.t ★ APCA.t SpPure Sp).
  Local Definition IstFull := (IstProd (IstSB (MutGA.t Sp).(Mod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_mutg:
    ISim.sim_fun open MutGAMod MutGIMod IstFull (fid MutHdr.mutg).
  Proof using _crisG APCInSp FInPure PureInSp.
    cStartFunSim. rewrite /MutGI.gF.
    
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
    cStepsS. cForceS vo. cStepsS. cForcesS. iSplitR; eauto.

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
    ISim.t open MutGAMod MutGIMod MutGA.init_cond IstFull.
  Proof.
    cStartModSim.
    - eapply simF_mutg.
    - iIntros "C". iFrame. do 4 iExists _. iPureIntro; esplits; eauto; set_solver.
  Qed.
End MutGIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ctxr (Sp SpPure : specmap)
    (APCInSp : APCA.sp ⊆ Sp)
    (GInPure : MutFA.SpF ⊆ SpPure)
    (PureInSp : SpPure ⊆ Sp) :
    ctx_refines
      (MutGI.t ★ APCA.t SpPure Sp, emp%I)
      (MutGA.t Sp ★ APCA.t SpPure Sp, MutGA.init_cond).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MutGIA.
