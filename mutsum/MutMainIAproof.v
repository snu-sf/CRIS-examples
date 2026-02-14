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
    ISim.sim_fun open MutMainAMod MutMainIMod IstFull None.
  Proof using APCInSp FInPure PureInSp.
    iStartSim.

    (* SRC: precondition *)
    steps_l. iDestruct "IST" as "%"; des; hss.

    (* SRC: handle pure (APC) *)
    rewrite /MutMainI.mainF /MutMainA.main_body /pure.
    force_l 11. steps_l.
    erewrite lookup_weaken; [| |eapply APCInSp]; cycle 1.
    { rewrite /APCA.sp; simpl_map; refl. }
    forces_l. iSplitR; eauto.
    steps_l.
    
    (* SRC: inlining APC *)
    inline_l. steps_l. iDestruct "ASM" as "[-> <-]"; hss.
    steps_l. rewrite /APC. force_l 1. steps_l.

    (* SRC, TGT: call mutg using APC tactic *)
    steps_r. apc_call ""; eauto.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). eapply OrdArith.lt_from_nat. nia. }
    { instantiate (1:=10). iSplit; eauto. 
      { iPureIntro. esplits; eauto; [unfold mut_max; nia|refl]. }
      { do 4 iExists _. iSplit; iPureIntro; esplits; eauto; unfold_mod; ss. }
    }
    iIntros (???) "ISTPOST".
    iDestruct "ISTPOST" as "[IST ->]".
    
    (* SRC: jump APC *)
    apc_l. steps_l. steps_r. hss. steps_r.
    forces_l. iSplitR; first done.
    steps_l. forces_l.

    (* SRC, TGT: prove the IST *)
    step. iSplitR "IST"; eauto.
    Unshelve. all: ss.
  (*SLOW*)Qed.

  Theorem sim:
    ISim.t open MutMainAMod MutMainIMod MutMainA.init_cond IstFull.
  Proof.
    init_sim.
    - apply simF_main; eauto.
    - iIntros "C". iFrame. do 4 iExists _; esplits; eauto.
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
  Proof using APCInSp FInPure PureInSp.
    eapply main_adequacy
      with (Ist := IstProd (IstSB MutMainA.scopes IstEq) IstEq).
    init_sim.
    (* { inv H. } *)
    { init_simF.
      steps_l. forces_r.
      iDestruct "IST" as "%"; des; hss.
      rewrite /MutMainA.main_body /pure /SModTr.trans_fnsem /SModTr.HoareFun. steps_r.
      erewrite lookup_weaken; [| |eapply APCInSp]; cycle 1.
      { rewrite /APCA.sp; simpl_map; refl. }
      steps_r. inline_r. forces_r.
      iDestruct "GRT" as "(% & %)". subst. iSplitR; et.
      hss. steps_r. forces_r. iSplitR; et.
      steps_r. steps_l. step. rewrite /ist_with_eq /IstProd. iSplit; eauto.
    }
    { rewrite /IstProd. iIntros "_". do 4 iExists _. eauto. }
  Unshelve. all: et.
  Qed.

End MutMainIA. End MutMainIA.
