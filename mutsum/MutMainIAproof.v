Require Import CRIS.
Require Import MutFA MutGA.
Require Import MutHeader MutMainI MutMainA.
Require Import APCHeader APC APCA APCC APCTactics.

Set Implicit Arguments.

Module MutMainIA. Section MutMainIA.
  Import MutAUX.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Context (Sp SpPure: specmap).
  Context (APCInSp : APCA.sp ⊆ Sp).
  Context (FInPure : MutFA.SpF ⊆ SpPure).
  Context (PureInSp : SpPure ⊆ Sp).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    (λ _ _, True)%I.

  Local Definition MutMainAMod := ((MutMainA.t true Sp) ★ APCA.t SpPure Sp).
  Local Definition MutMainIMod := ((MutMainI.t) ★ APCA.t SpPure Sp).
  Local Definition IstFull := (IstProd (IstSB (MutMainA.t true Sp).(Mod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_main:
    ISim.sim_fun open MutMainAMod MutMainIMod IstFull entry.
  Proof using APCInSp FInPure PureInSp.
    cStartFunSim.

    (* SRC: precondition *)
    cStepsS. iDestruct "IST" as "%"; des; cSimpl.

    (* SRC: handle pure (APC) *)
    rewrite /MutMainI.mainF /MutMainA.main_body /pure.
    cForceS 11. cStepsS.
    erewrite lookup_weaken; [| |eapply APCInSp]; cycle 1.
    { rewrite /APCA.sp; simpl_map; refl. }
    cForcesS. iSplitR; eauto.
    cStepsS.
    
    (* SRC: inlining APC *)
    cInlineS. cStepsS. iDestruct "ASM" as "[-> <-]"; cSimpl.
    cStepsS. rewrite /APC. cForceS 1. cStepsS.

    (* SRC, TGT: cCall mutg using APC tactic *)
    cStepsT. apcCall ""; eauto.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). iSplit; eauto. 
      { iPureIntro. esplits; eauto; [unfold mut_max; nia|refl]. }
      { do 4 iExists _. iSplit; iPureIntro; esplits; eauto; unfold_mod; ss. }
    }
    iIntros (???) "ISTPOST".
    iDestruct "ISTPOST" as "[IST ->]".
    
    (* SRC: jump APC *)
    apcS. cStepsS. cStepsT. cSimpl. cStepsT.
    cForcesS. iSplitR; first done.
    cStepsS. cForcesS.

    (* SRC, TGT: prove the IST *)
    cStep. iSplitR "IST"; eauto.
    Unshelve. all: ss.
  (*SLOW*)Qed.

  Theorem sim:
    ISim.t open MutMainAMod MutMainIMod MutMainA.init_cond IstFull.
  Proof.
    cStartModSim.
    - apply simF_main; eauto.
    - iIntros "C". iFrame. do 4 iExists _; esplits; eauto.
  Qed.

  Theorem ctxr:
    ctx_refines
      (MutMainI.t ★ APCA.t SpPure Sp, emp%I)
      (MutMainA.t true Sp ★ APCA.t SpPure Sp, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.

  Theorem ctxr_close:
    ctx_refines
      (MutMainA.t true  Sp ★ APCC.t Sp, emp%I)
      (MutMainA.t false Sp ★ APCC.t Sp, emp%I).
  Proof using APCInSp FInPure PureInSp.
    eapply main_adequacy
      with (Ist := IstProd (IstSB MutMainA.scopes IstEq) IstEq).
    cStartModSim.
    (* { inv H. } *)
    { cStartFunSim.
      cStepsS. cForcesT.
      iDestruct "IST" as "%"; des; cSimpl.
      rewrite /MutMainA.main_body /pure /SModTr.trans_fnsem /SModTr.HoareFun. cStepsT.
      erewrite lookup_weaken; [| |eapply APCInSp]; cycle 1.
      { rewrite /APCA.sp; simpl_map; refl. }
      cStepsT. cInlineT. cForcesT.
      iDestruct "GRT" as "(% & %)". subst. iSplitR; et.
      cSimpl. cStepsT. cForcesT. iSplitR; et.
      cStepsT. cStepsS. cStep. rewrite /ist_with_eq /IstProd. iSplit; eauto.
    }
    { rewrite /IstProd. iIntros "_". do 4 iExists _. eauto. }
  Unshelve. all: et.
  Qed.

End MutMainIA. End MutMainIA.
