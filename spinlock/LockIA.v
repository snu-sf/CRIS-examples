Require Import CRIS.
From CRIS.spinlock Require Import Header LockI LockA.
Require Import ImpPrelude MemA.
Require Import SchHeader SchA SchTactics.

Module LockIA. Section LockIA.
  Import LockAS.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG, !spinlockG}.

  Context (E : coPset) (Hsub : ↑N_SpinLockA ⊆ E).
  Context (tidq : Qp).
  Context (sp_user : spl_type).
  Context (sp : sp_type).
  Context (SchInSp : sp_incl (SchAS.sp sp_user E tidq) sp).

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemP := MemP.t.
  Local Definition SpinLockA := (SpinLockA.t E tidq sp).
  Local Definition SpinLockI := (SpinLockI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockA ★ MemP).
  Local Notation MI := (SpinLockI ★ MemP).

  Lemma newlock_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.newlock).
  Proof using SchInSp Hsub.
    init_simF.

    (* preprocess initial conditions *)
    steps_l. rename _q1 into tid, _q into vret. destruct _q2 as [n P]; s.
    iDestruct "ASM" as "[TID [P ->]]". hss.
    steps_r.

    (* tgt yield *)
    sch_yield_ir; iFrame; sch_intros.

    (* tgt inline - mem alloc *)
    steps_r. inline_r. steps_r.
    rewrite /fspec_proph_update; unfold_iter_r; steps_r; hss_r; steps_r.
    iApply wsim_update_proph_tgt; iExists 1. iSplit; eauto.
    iIntros (?) "[%blk [% [PT _]]]". steps_r. hss_r; steps_r.

    (* tgt yield *)
    sch_yield_ir; iFrame; sch_intros.

    (* tgt inline - mem store *)
    steps_r. inline_r. steps_r.
    rewrite /fspec_proph_update; unfold_iter_r; steps_r; hss_r; steps_r.
    iApply wsim_update_proph_tgt; iExists (blk, 0%Z, _, Vint 0). s. iSplitL "PT"; s; et.
    iIntros (?) "[PT %]". steps_r.
    hss. steps_r.

    (* src/tgt yield *)
    sch_yield_ir; iFrame; sch_intros.
    sch_yield_l. force_l (Vptr (blk, 0%Z)). steps_l. force_l.

    (* prove source postcondition *)
    (* alloc invariant *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].
    iMod (inv_alloc (LockAS.lock_inv (blk, 0%Z) P γ) _ _ _ N_SpinLockA with "[P PT TKN]") as "#I"; eauto.
    { rewrite /lock_inv /=; SL_red; iRight; iFrame. }
    forces_l. iFrame. iSplit; eauto.
    { iSplit; eauto. rewrite /is_lock. iExists _, _; iSplit; eauto. }
    steps_l. step. eauto.
  (*SLOW*)Admitted.

  Lemma acquire_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.acquire).
  Proof using SchInSp Hsub.
    init_simF.

    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[TID [[-> #LOCK] ->]]". hss.
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs]. steps_r.

    (* start coinduction for lock acquire/failure *)
    iApply wsim_reset.
    iStopProof. revert nths. clear NODS NODT.
    combine_quant st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' [st_sgt [st_src nths]]) "[#LOCK [IST TID]] _ #CIH /=".

    unfold_iter_r. steps_r.
    (* tgt yield *)
    sch_yield_ir; iFrame; sch_intros.
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl". SL_red.
    iDestruct "I" as "[FAIL|SUCC]".
    { (* fail case *)
      (* tgt inline - mem cas *)
      steps_r. inline_r. steps_r.
      rewrite /fspec_proph_update; unfold_iter_r; steps_r; hss_r; steps_r.
      iApply wsim_update_proph_tgt; iExists (_,_,_,_,_,_,_,_,_,_); s.
      iSplitL "FAIL". { iFrame. et. }
      iIntros (?) "[% [POINTS_TO _]]". steps_r.
      hss. steps_r.
      iMod ("Hcl" with "[POINTS_TO]") as "_". { iFrame. }
      (* tgt yields *)
      sch_yield_ir; iFrame; sch_intros.
      sch_yield_ir; iFrame; sch_intros.
      steps_r. by_coind "CIH". iFrame. done.
    }
    { (* success case *)
      (* tgt inline - mem cas *)
      iDestruct "SUCC" as "[POINTS_TO [Q TKN]]".
      steps_r. inline_r. steps_r.
      rewrite /fspec_proph_update; unfold_iter_r; steps_r; hss_r; steps_r.
      iApply wsim_update_proph_tgt; iExists (_,_,_,_,_,_,_,_,_,_); s.
      iSplitL "POINTS_TO". { iFrame; et. }
      iIntros (?) "[% [POINTS_TO _]]". steps_r.
      hss. steps_r.
      iMod ("Hcl" with "[POINTS_TO]") as "_". { iFrame. }
      (* tgt yields *)
      do 3 (sch_yield_ir; iFrame; sch_intros).
      (* src yield *)
      sch_yield_l. forces_l. iSplitL "Q TKN TID"; SL_red; iFrame; et.
      (* both terminate *)
      step; eauto.
    }
    Unshelve. all: eauto. all: try exact 1%Qp. all: try exact Vundef.
  (*SLOW*)Admitted.

  Lemma release_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.release).
  Proof using SchInSp Hsub.
    init_simF.
    (* process src precondition *)
    steps_l.
    iDestruct "ASM" as "[TID [(% & #LOCK & TKN & Q) %]]".
    iDestruct "LOCK" as (?) "[% LOCK]". destruct bofs as [blk ofs].
    hss.
    steps_r.
    (* tgt yield *)
    sch_yield_ir; iFrame; sch_intros.
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl". SL_red.
    iDestruct "I" as "[LOCKED|UNLOCKED]".
    { (* locked case *)
      steps_r. inline_r. steps_r.
      rewrite /fspec_proph_update; unfold_iter_r; steps_r; hss_r; steps_r.
      iApply wsim_update_proph_tgt; iExists (_,_,_,_); s.
      iSplitL "LOCKED"; iFrame; et.
      iIntros (?) "[POINTS_TO %]".
      hss. steps_r.
      iMod ("Hcl" with "[POINTS_TO Q TKN]") as "_". iRight. iFrame. hss_r; steps_r.
      (* tgt yield *)
      sch_yield_ir; iFrame; sch_intros.
      (* src yield *)
      sch_yield_l. steps_l. forces_l. iFrame. iSplit; et. step. iFrame; et.
    }
    { (* unlocked case - ex falso quodlibet *)
      iDestruct "UNLOCKED" as "[POINTS_TO [Q' TKN']]".
      iCombine "TKN TKN'" gives %Hv. done.
    }
  (*SLOW*)Admitted.

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { split; et. }
    { apply newlock_simF. }
    { apply acquire_simF. }
    { apply release_simF. }
  Qed.

  (* ctxr works as a unit in compositions of module simulations *)
  Lemma ctxr :
    ctx_refines
      (SpinLockA.t E tidq sp ★ MemP.t, emp%I)
      (SpinLockI.t           ★ MemP.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End LockIA. End LockIA.
