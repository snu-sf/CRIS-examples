Require Import CRIS.
Require Import LockHeader MainI MainA LockI LockA.
Require Import ImpPrelude.
Require Import SchHeader SchA MemA SchTactics MemTactics.
From iris Require Import frac_auth numbers.

Module MainIA. Section MainIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !spinlockG, !spinlockmainG}.
  Import LockA MainA.

  Context (N : namespace).
  Context (sp_s sp_t sp_user_s sp_user_t : specmap). (* sps of lock/sch/mem *)
  Context (SchInSp_s : (SchA.sp sp_user_s (↑N)) ⊆ sp_s).
  Context (SchInSp_t : (SchA.sp sp_user_t (↑N)) ⊆ sp_t).
  Context (MainInSp : (MainA.sp (↑N)) ⊆ sp_user_s).

  Local Definition MemA := MemA.t sp_s.
  Local Definition SpinLockA := (LockA.t (↑N) sp_t).
  Local Definition SpinLockMainA := (MainA.t N sp_s).
  Local Definition SpinLockMainI := (SpinLockMainI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockMainA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockMainA ★ (SpinLockA ★ MemA)).
  Local Notation MI := (SpinLockMainI ★ (SpinLockA ★ MemA)).

  Lemma incr_simF : ISim.sim_fun open MA MI IstFull (fid SpinLockMainHdr.incr).
  Proof using SchInSp_s SchInSp_t MainInSp.
    cStartFunSim. rewrite /SpinLockMainI.incr /incr /sfunN /sfunU.
    (* process src precondition *)
    cStepsS. destruct _q as [[stid mtid] [[[blk_l ofs_l] [blk_v ofs_v]] γ_v]].
    iDestruct "ASM" as "[TID [-> [-> [%γ_l [#Lock Tkn]]]]]".
    cStepsS; cStepsT.

    (* main code *)
    rewrite /incr /SpinLockMainI.incr. cStepsS. cStepsT.
    (* tgt yields *)
    sYieldIR "IST" "TID". sYieldIR "IST" "TID".

    (* tgt inline - lock acquire *)
    cInlineT.
    cForceT (_, _, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))).
    cStepsT. cForcesT.
    (* rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]". *)
    iFrame "TID Lock". iSplit; eauto. cStepsT.
    sYieldII "IST". cStepsT.

    (* success case *)
    iDestruct "GRT" as "[TID [<- [_ [TKN P]]]]". cStepsT.
    sYieldIR "IST" "TID".

    (* tgt yield *)
    solve_base_sl_red. iDestruct "P" as "[%x [PT P]]".
    mLoad.
    sYieldIR "IST" "TID". sYieldIR "IST" "TID".

    mStore.
    sYieldIR "IST" "TID".

    iCombine "P Tkn" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    cInlineT. cStepsT.
    cForceT (_, _, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))). cForcesT.
    iSplitL "TID F PT TKN".
    { solve_base_sl_red. iFrame. iSplit; eauto. }
    cStepsT. sYieldII "IST". cStepsT.
    
    (* tgt inline - lock acquire - restore lock protected proposition *)
    iDestruct "GRT" as "[TID [<- _]]". cStepsT.
    (* iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2. *)
    sYieldIR "IST" "TID".
    (* src yield *)
    sYieldS. cStepsS. cForcesS. iFrame; iSplit; eauto.
    (* both terminate *)
    cStep. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma main_simF : ISim.sim_fun open MA MI IstFull entry.
  Proof using SchInSp_s SchInSp_t MainInSp.
    cStartFunSim. rewrite /SpinLockMainI.main /main /sfunN /sfunU.
    
    cStepsS. destruct _q as [[stid mtid] []]. iDestruct "ASM" as "[TID ->]".

    rewrite /main. cStepsS.
    cStepsT. rewrite /SpinLockMainI.main. cStepsT.
    rewrite /Sch.spawn.

    (* tgt yield *)
    sYieldIR "IST" "TID".

    (* tgt inline - mem alloc - counter allocation *)
    iApply wsim_mem_alloc; ss. iIntros (blk) "[↦ _]". cStepsT.
    sYieldIR "IST" "TID".

    (* tgt inline - mem store - counter initialization *)
    iApply (wsim_mem_store with "[↦]"); ss. iIntros"↦". cStepsT.
    sYieldIR "IST" "TID".

    (* create lock-guarded proposition *)
    iMod (own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)) as "[%γ [B W]]". { eapply frac_auth_valid; ss. }

    (* tgt inline - newlock *)
    cInlineT. cForceT (stid, mtid, existT 0 (lock_P (blk, 0%Z) γ)). cForcesT.
    iSplitL "TID B ↦"; eauto.
    { iFrame. solve_base_sl_red. iFrame. done. }
    cStepsT.

    (* src/tgt yields *)
    sYieldII "IST".
    cStepsT. iDestruct "GRT" as "[TID [-> [%val [%γl [-> [%bofs_l [-> #Lock]]]]]]]".
    cStepsT.
    sYieldIR "IST" "TID".

    (* iPoseProof "I" as "[%bofs_l [-> _]]". *)
    sYieldS. cForceS (Vptr bofs_l, Vptr (blk, 0%Z)). cStepsS. sYieldS.
    (* create preconditions of incr *)
    iDestruct "W" as "[W1 W2]".

    (* spawn thread 1 - incr *)
    rewrite /Sch.spawn. cStepsS. simpl_sp. cForceS (_,_). cForcesS. iSplitL "W1".
    { iExists _, _, _. iSplit; et. iSplitR.
      - iExists _; iSplit; [iPureIntro; simpl_sp|]; ss. iApply incr_spawnable.
      - iFrame "W1"; eauto. repeat iSplit; eauto. iExists _; iFrame "Lock"; auto.
    }
    cStepsT. cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsS. iDestruct "ASM" as "[% [[-> ->] TKN1]]". 
    cStepsT. cStepsS.
    sYieldIR "IST" "TID". sYieldS.

    (* spawn thread 2 - incr *)
    rewrite /Sch.spawn.
    cStepsS. simpl_sp. cForceS (_,_). cForcesS. iSplitL "W2".
    { iExists _, _, _. iSplit; et. iSplitR.
      - iExists _; iSplit; [iPureIntro; simpl_sp|]; ss. iApply incr_spawnable.
      - iFrame "W2"; eauto. repeat iSplit; eauto. iExists _; iFrame "Lock"; auto.
    }
    cStepsT. cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsS. iDestruct "ASM" as "[% [[-> ->] TKN2]]". 
    cStepsT. cStepsS.
    sYieldIR "IST" "TID". sYieldS.

    (* join thread 1 - incr *)
    rewrite /Sch.join.
    cStepsS. simpl_sp. cForceS (_,_,_). cForcesS. iSplitL "TKN1 TID".
    { iFrame. eauto. }
    cStepsT. cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsS. iDestruct "ASM" as "[TID [% [% [[-> ->] W1]]]]". solve_base_sl_red.
    cStepsS; cStepsT.
    sYieldIR "IST" "TID". sYieldS. rewrite /Sch.join. cStepsT. cStepsS. simpl_sp.

    (* join thread 2 - incr *)
    cForceS (stid, mtid, _). cForcesS. iSplitL "TID TKN2".
    { iFrame; eauto. }
    cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsS. iDestruct "ASM" as "[TID [% [% [[-> ->] W2]]]]". solve_base_sl_red. cStepsT.
    cStepsS; cStepsT.
    sYieldIR "IST" "TID".

    (* tgt inline - lock acquire *)
    cInlineT. cStepsT.
    cForceT (_, _, (γl, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). cForcesT.
    iFrame "TID"; iSplitR.
    { repeat iSplit; eauto. iFrame "Lock"; auto. }
    cStepsT.
    sYieldII "IST". cStepsT.
    iDestruct "GRT" as "[TID [<- [_ [TKN P]]]]". cStepsT.
    sYieldIR "IST" "TID".
    iCombine "W1 W2" as "W". solve_base_sl_red.
    iDestruct "P" as "[%x [PT B]]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.

    (* tgt inline - mem load *)
    mLoad.

    (* tgt yield *)
    sYieldIR "IST" "TID". sYieldIR "IST" "TID".

    (* tgt inline - lock release *)
    cInlineT.
    cForceT (_, _, (γl, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). cForcesT.
    iSplitL "TKN TID B PT".
    { solve_base_sl_red. iFrame. iFrame "Lock"; iSplit; eauto. }
    cStepsT.

    (* tgt yield *)
    sYieldII "IST". cStepsT. iDestruct "GRT" as "[TID [<- _]]". cStepsT.
    sYieldIR "IST" "TID".

    (* both output - counter value *)
    sYieldS. cStep.
    cStepsS. cStepsT.
    sYieldIR "IST" "TID". sYieldS.
    (* terminate both *)
    cForcesS. iFrame; iSplit; first eauto. cStep. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    cStartModSim.
    { eapply main_simF. }
    { eapply incr_simF. }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.

  Lemma ctxr :
    ctx_refines
      ((SpinLockMainI.t) ★ ((LockA.t (↑N) sp_t) ★ MemA.t sp_s), emp%I)
      ((MainA.t N sp_s)  ★ ((LockA.t (↑N) sp_t) ★ MemA.t sp_s), emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End MainIA. End MainIA.
