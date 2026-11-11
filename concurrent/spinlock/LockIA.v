Require Import CRIS.common.CRIS.
From CRIS.imp_system Require Import imp.ImpPrelude mem.MemA mem.MemTactics.
From CRIS.spinlock Require Import LockHeader LockI LockA.
From CRIS.scheduler Require Import SchHeader SchA SchTactics.

Module LockIA. Section LockIA.
  Import LockA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !spinlockG}.

  Context (E : coPset) (Hsub : ↑N_SpinLockA ⊆ E).
  Context (sp_user sp : specmap).
  Context (SchInSp : (SchA.sp sp_user E) ⊆ sp).

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemA := MemA.t sp.
  Local Definition SpinLockA := (LockA.t E sp).
  Local Definition SpinLockI := (SpinLockI.t).
  Local Notation MA := (SpinLockA ★ MemA).
  Local Notation MI := (SpinLockI ★ MemA).
  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Local Definition IstFull : iProp Σ :=
    (True ∗ IstEq MemA)%I.

  Lemma newlock_simF :
    ⊢ ISim.sim_fun open MA MI IstFull (fid SpinLockHdr.newlock).
  Proof using SchInSp Hsub.
    cStartFunSim. rewrite /SpinLockI.newlock /newlock.

    (* preprocess initial conditions *)
    cStepsS. destruct _q as [[stid mtid] [n P]].
    iDestruct "ASM" as "[TID [-> P]]"; s. destruct Any.downcast; s; [|cStepS; ss].
    cStepsT. cNormS.

    (* tgt yield *)
    sYieldIR "IST" "TID".

    (* tgt inline - mem alloc *)
    mAllocT as (blk) "[↦ _]".

    (* tgt yield *)
    sYieldIR "IST" "TID".

    (* tgt inline - mem store *)
    mStore.

    (* src/tgt yield *)
    sYieldIR "IST" "TID".
    sYieldS. cForceS (Vptr (blk, 0%Z)). cStepsS.

    (* prove source postcondition *)
    (* alloc invariant *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].
    iMod (inv_alloc (LockA.lock_inv (blk, 0%Z) P γ) _ _ _ N_SpinLockA with "[P ↦ TKN]")
      as "#I"; eauto.
    { solve_base_sl_red. iRight; iFrame. }
    cForcesS. iFrame. iSplit; eauto.
    { iSplit; eauto. rewrite /is_lock. iExists _, _; iSplit; eauto. }
    cStep. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma acquire_simF :
    ⊢ ISim.sim_fun open MA MI IstFull (fid SpinLockHdr.acquire).
  Proof using SchInSp Hsub.
    cStartFunSim. rewrite /SpinLockI.acquire /acquire.

    (* process src precondition *)
    cStepsS. destruct _q as [[stid mtid] [[γ vlk] [n P]]].
    iDestruct "ASM" as "[TID [-> [-> #LOCK]]]".
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs]; subst.
    cStepsT. cStepsS.

    (* start coinduction for lock acquire/failure *)
    iApply wsim_reset.
    cCoind CIH g' __ with blk ofs. iIntros "[#LOCK [IST TID]] /=".
    cNormT. rewrite unfold_iterC. cStepsT.
    (* tgt yield *)
    sYieldIR "IST" "TID".
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl".
    iDestruct "I" as "[FAIL|SUCC]".
    { (* fail case *)
      (* tgt inline - mem cas *)
      mCas.
      instantiate (1:=emp%I).
      iSplitR; first done. iSplitR.
      { ss. iIntros "_ !>"; eauto. }
      iIntros "↦ _"; case_decide; first done.
      iMod ("Hcl" with "[↦]") as "_". { iFrame. }
      cStepsT.
      
      (* tgt yields *)
      sYieldIR "IST" "TID". sYieldIR "IST" "TID".
      cByCoind CIH. iFrame. done.
    }
    { (* success case *)
      (* tgt inline - mem cas *)
      cStepsT.
      iDestruct "SUCC" as "[↦ [Q TKN]]".
      mCas.
      instantiate (1:=emp%I).
      iSplitR; first done. iSplitR.
      { ss. iIntros "_ !>"; eauto. }
      iIntros "↦ _"; case_decide; last done.
      iMod ("Hcl" with "[↦]") as "_". { iFrame. }
      cStepsT.

      (* tgt yields *)
      do 3 (sYieldIR "IST" "TID").

      (* src yield *)
      sYieldS. cForcesS. iSplitL "Q TKN TID".
      { solve_base_sl_red; iFrame; repeat iSplit; et. rewrite /token. solve_base_sl_red. }
      (* both terminate *)
      cStep; iFrame; eauto.
    }
  Unshelve. all: try exact 1%Qp. all: try exact Vundef.
  (*SLOW*)Qed.

  Lemma release_simF :
    ⊢ ISim.sim_fun open MA MI IstFull (fid SpinLockHdr.release).
  Proof using SchInSp Hsub.
    cStartFunSim. rewrite /SpinLockI.release /release.
    (* process src precondition *)
    cStepsS. destruct _q as [[stid mtid] [[γ vlk] [n P]]].
    iDestruct "ASM" as "[TID (% & % & #LOCK & TKN & Q)]".
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs]. subst.
    cStepsS; cStepsT.
    (* tgt yield *)
    sYieldIR "IST" "TID".
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl".
    iDestruct "I" as "[LOCKED|UNLOCKED]".
    { (* locked case *)
      cStepsT. cInlineT. cStepsT.
      cForceT (_,_,_,_). cForcesT.
      iSplitL "LOCKED"; iFrame; et.
      cStepsT. iDestruct "GRT" as "[% [PT %]]"; subst.
      cStepsT.
      iMod ("Hcl" with "[PT Q TKN]") as "_".
      { iRight. rewrite /token; solve_base_sl_red. iFrame. solve_base_sl_red. }
      (* tgt yield *)
      sYieldIR "IST" "TID".
      (* src yield *)
      sYieldS. cStepsS. cForcesS. iFrame. iSplit; et. cStep. iFrame; et.
    }
    { (* unlocked case - ex falso quodlibet *)
      iDestruct "UNLOCKED" as "[PT [Q' TKN']]".
      solve_base_sl_red.
      iCombine "TKN TKN'" gives %Hv. done.
    }
  (*SLOW*)Qed.

  End SIM_FUNS.

  (* Construct ISim.t for summing up each simulation proofs *)

  Lemma sim : init_cond ⊢ ISim.t open MA MI.
  Proof.
    iIntros "_".
    iApply (ISim_reflR open SpinLockA SpinLockI MemA (λ _, True%I)).
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT". done.
    - iIntros (STATE). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split; mod_tac. }
      iIntros (fn) "%Hfn".
      set_unfold in Hfn; des; subst.
      + iApply newlock_simF.
      + iApply acquire_simF.
      + iApply release_simF.
  Qed.

  (* ctxr works as a unit in compositions of module simulations *)
  Lemma ctxr :
    ⊢ ctx_refines
        (SpinLockI.t ★ MemA.t sp)
        (LockA.t E sp ★ MemA.t sp).
  Proof. iApply main_adequacy. iApply sim; eauto. Qed.
End LockIA. End LockIA.
