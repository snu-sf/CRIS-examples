Require Import CRIS.
Require Import ImpPrelude MemA MemTactics.
Require Import LockHeader LockI LockA.
Require Import SchHeader SchA SchTactics.

Module LockIA. Section LockIA.
  Import LockA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS, _SPINLOCK: !spinlockG}.

  Context (E : coPset) (Hsub : ↑N_SpinLockA ⊆ E).
  Context (sp_user sp : specmap).
  Context (SchInSp : (SchA.sp sp_user E) ⊆ sp).

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemA := MemA.t sp.
  Local Definition SpinLockA := (LockA.t E sp).
  Local Definition SpinLockI := (SpinLockI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockA ★ MemA).
  Local Notation MI := (SpinLockI ★ MemA).

  Lemma newlock_simF : ISim.sim_fun open MA MI IstFull (fid SpinLockHdr.newlock).
  Proof using SchInSp Hsub.
    iStartSim. rewrite /SpinLockI.newlock /newlock.

    (* preprocess initial conditions *)
    steps_l. destruct _q as [[stid mtid] [n P]].
    iDestruct "ASM" as "[TID [-> P]]"; s. destruct Any.downcast; s; [|step_l; ss].
    steps_r. step_l.

    (* tgt yield *)
    sch_yield_ir "IST" "TID".

    (* tgt inline - mem alloc *)
    iApply wsim_mem_alloc; ss.
    iIntros (blk) "[↦ _]". steps_r.

    (* tgt yield *)
    sch_yield_ir "IST" "TID".

    (* tgt inline - mem store *)
    store_r "↦".

    (* src/tgt yield *)
    sch_yield_ir "IST" "TID".
    sch_yield_l. force_l (Vptr (blk, 0%Z)). steps_l.

    (* prove source postcondition *)
    (* alloc invariant *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].
    iMod (inv_alloc (LockA.lock_inv (blk, 0%Z) P γ) _ _ _ N_SpinLockA with "[P ↦ TKN]")
      as "#I"; eauto.
    { solve_base_sl_red. iRight; iFrame. }
    forces_l. iFrame. iSplit; eauto.
    { iSplit; eauto. rewrite /is_lock. iExists _, _; iSplit; eauto. }
    step. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma acquire_simF : ISim.sim_fun open MA MI IstFull (fid SpinLockHdr.acquire).
  Proof using SchInSp Hsub.
    iStartSim. rewrite /SpinLockI.acquire /acquire.

    (* process src precondition *)
    steps_l. destruct _q as [[stid mtid] [[γ vlk] [n P]]].
    iDestruct "ASM" as "[TID [-> [-> #LOCK]]]".
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs]; subst.
    steps_r. steps_l.

    (* start coinduction for lock acquire/failure *)
    iApply wsim_reset.
    iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#LOCK [IST TID]] /=".
    destruct_quant CIH.

    unfold_iterC_r. steps_r.
    (* tgt yield *)
    sch_yield_ir "IST" "TID".
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl".
    iDestruct "I" as "[FAIL|SUCC]".
    { (* fail case *)
      (* tgt inline - mem cas *)
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "FAIL"); ss.
      { ss. iIntros "_ !>"; eauto. }
      iIntros "↦ _"; case_decide; first done.
      iMod ("Hcl" with "[↦]") as "_". { iFrame. }
      steps_r.
      
      (* tgt yields *)
      sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
      by_coind CIH. iFrame. done.
    }
    { (* success case *)
      (* tgt inline - mem cas *)
      steps_r.
      iDestruct "SUCC" as "[↦ [Q TKN]]".
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "↦"); ss.
      { ss. iIntros "_ !>"; eauto. }
      iIntros "↦ _"; case_decide; last done.
      iMod ("Hcl" with "[↦]") as "_". { iFrame. }
      steps_r.

      (* tgt yields *)
      do 3 (sch_yield_ir "IST" "TID").

      (* src yield *)
      sch_yield_l. forces_l. iSplitL "Q TKN TID".
      { solve_base_sl_red; iFrame; repeat iSplit; et. rewrite /token. solve_base_sl_red. }
      (* both terminate *)
      step; iFrame; eauto.
    }
  Unshelve. all: try exact 1%Qp. all: try exact Vundef.
  (*SLOW*)Qed.

  Lemma release_simF : ISim.sim_fun open MA MI IstFull (fid SpinLockHdr.release).
  Proof using SchInSp Hsub.
    iStartSim. rewrite /SpinLockI.release /release.
    (* process src precondition *)
    steps_l. destruct _q as [[stid mtid] [[γ vlk] [n P]]].
    iDestruct "ASM" as "[TID (% & % & #LOCK & TKN & Q)]".
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs]. subst.
    steps_l; steps_r.
    (* tgt yield *)
    sch_yield_ir "IST" "TID".
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl".
    iDestruct "I" as "[LOCKED|UNLOCKED]".
    { (* locked case *)
      steps_r. inline_r. steps_r.
      force_r (_,_,_,_). forces_r.
      iSplitL "LOCKED"; iFrame; et.
      steps_r. iDestruct "GRT" as "[% [PT %]]"; subst.
      steps_r.
      iMod ("Hcl" with "[PT Q TKN]") as "_".
      { iRight. rewrite /token; solve_base_sl_red. iFrame. solve_base_sl_red. }
      (* tgt yield *)
      sch_yield_ir "IST" "TID".
      (* src yield *)
      sch_yield_l. steps_l. forces_l. iFrame. iSplit; et. step. iFrame; et.
    }
    { (* unlocked case - ex falso quodlibet *)
      iDestruct "UNLOCKED" as "[PT [Q' TKN']]".
      solve_base_sl_red.
      iCombine "TKN TKN'" gives %Hv. done.
    }
  (*SLOW*)Qed.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { apply newlock_simF. }
    { apply acquire_simF. }
    { apply release_simF. }
    { iIntros "$"; iExists _, _, _, _; iFrame; eauto. }
  Qed.

  (* ctxr works as a unit in compositions of module simulations *)
  Lemma ctxr :
    ctx_refines
      (LockA.t E sp ★ MemA.t sp, emp%I)
      (SpinLockI.t  ★ MemA.t sp, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End LockIA. End LockIA.
