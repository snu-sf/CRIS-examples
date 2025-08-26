Require Import CRIS.
Require Import ImpPrelude MemA.
Require Import SchHeader SchA SchTactics.
From CRIS.spinlock Require Import Header LockI LockA.

Module LockIA. Section LockIA.
  Import LockAS.
  Context `{CrisG: !crisG Γ Σ α β τ _S _I}.
  Context `{MemG: !memG}.
  Context `{SchG: !schG}.
  Context `{SpinlockG: !spinlockG}.

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemA := MemA.t.
  Local Definition SpinLockA := SpinLockA.t.
  Local Definition SpinLockI := SpinLockI.t.
  Local Definition IstFull := (IstProd (IstSB (Mod.scopes SpinLockA) IstTrue) IstEq).
  Local Notation MA := (SpinLockA ★ MemA).
  Local Notation MI := (SpinLockI ★ MemA).

  Lemma newlock_simF :
    ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.newlock).
  Proof using SchG.
    init_simF.

    (* preprocess initial conditions *)
    steps_l. unfold_iter_l. steps_l.
    destruct (arg↓) as [v|] eqn:E; cycle 1.
    { sch_yield_l. steps_l. destruct _q.
      iDestruct "ASM" as "[[% _] _]". des; subst. hss.
    }

    (* tgt yield *)
    steps_r. sch_yield_rr.

    (* tgt inline - mem alloc *)
    steps_r. inline_r. steps_r. force_r 1. forces_r.
    iSplit; et.
    steps_r. iDestruct "GRT" as "[[%blk [-> [↦ _]]] ->]".
    hss_r; steps_r.

    (* tgt yield *)
    sch_yield_rr.

    (* tgt inline - mem store *)
    steps_r. inline_r. steps_r. force_r (blk, 0%Z, _, _); s. steps_r. forces_r.
    iFrame "↦". iSplit; try done.
    steps_r. iDestruct "GRT" as "[[↦ ->] ->]".
    hss_r; steps_r.

    (* src/tgt yield *)
    sch_yield_rr. sch_yield_l; steps_l.

    force_l true. force_l ((Vptr (blk, 0%Z))↑). steps_l. destruct _q as [n P]. s.
    iDestruct "ASM" as "[[% P] _]". des. hss.

    (* lock token allocation *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].
    iMod (inv_alloc (LockAS.lock_inv (blk, 0%Z) P γ) _ _ _ N_SpinLockA
      with "[↦ P TKN]") as "#I"; ss.
    { rewrite /lock_inv; SL_red; iRight; iFrame. }
    forces_l.
    iSplitR; cycle 1.
    { steps_l. sch_yield_l. step. iSplit; done. }
    iSplit; eauto. iExists _, _; iSplit; eauto.
    rewrite /is_lock; iExists _; iFrame "I"; done.
    Unshelve. all: exact 0.
  (*SLOW*)Qed.

  Lemma acquire_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.acquire).
  Proof using SchG.
    init_simF.

    (* process src precondition *)
    steps_l; unfold_iter_l; steps_l. 
    
    (* ill-formed argument *)
    destruct (classic (∃ blk ofs, arg = [Vptr (blk,ofs)]↑)); cycle 1.
    { sch_yield_l. steps_l. destruct _q1. iDestruct "ASM" as "[[% L] _]".
      subst. iDestruct "L" as "[% [% _]]". destruct bofs. subst. exfalso. et.
    }
    des; subst; hss.

    steps_r; unfold_iter_r; steps_r.    
    (* start coinduction for lock acquire/failure *)    
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "IST /=".
    destruct_quant CIH.

    sch_yield_rr; sch_yield_l; steps_l.
    steps_r; inline_r; steps_r.

    destruct _q1. s. iDestruct "ASM" as "[[% [% [% #I]]] _]"; des; subst. hss.
    iInv "I" as "INV" "ACC". iEval (SL_red) in "INV".
    iDestruct "INV" as "[PT | [PT [R TKN]]]".
    { force_r (_, _, _, _, _, _, _, _, _, _). steps_r. forces_r.
      iSplitL "PT".
      { iFrame. et. }
      steps_r. iDestruct "GRT" as "[[% [↦ _]] %]"; subst. hss.
      steps_r. iMod ("ACC" with "[↦]") as "_".
      { SL_red; iFrame "↦". }
      force_l true. forces_l. iSplitL "".
      { repeat (iSplit; et). iExists _; et. }
      steps_l. unfold_iter_l; steps_l.
      sch_yield_rr. steps_r. sch_yield_rr. steps_r.
      unfold_iter_r; steps_r.
      by_coind CIH. hss_copset. iFrame.
    }
    { force_r (_, _, _, _, _, _, _, _, _, _). steps_r. forces_r.
      iSplitL "PT".
      { iFrame. repeat (iSplit; et). }
      steps_r. iDestruct "GRT" as "[[% [↦ _]] %]"; subst. hss.
      steps_r. iMod ("ACC" with "[↦]") as "_".
      { SL_red; iFrame "↦". }
      force_l false. forces_l. iSplitL "R TKN".
      { repeat (iSplit; et). SL_red. iFrame. }
      steps_l. sch_yield_rr. steps_r. sch_yield_rr. steps_r.
      sch_yield_rr. steps_r. sch_yield_l.
      step; et.
    }      
  Unshelve. all: try exact 1%Qp; try exact (Vint 0); eauto.
  (*SLOW*)Qed.

  Lemma release_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.release).
  Proof using SchG.
    init_simF.
    (* process src precondition *)
    steps_l; unfold_iter_l; steps_l.

    (* ill-formed argument *)
    destruct (classic (∃ blk ofs, arg = [Vptr (blk,ofs)]↑)); cycle 1.
    {  sch_yield_l. steps_l. destruct _q1. iDestruct "ASM" as "[[% [L _]] _]".
      subst. iDestruct "L" as "[% [% _]]". destruct bofs. subst. exfalso. et.
    }
    des; subst; hss.

    steps_r; sch_yield_rr; steps_r.
    sch_yield_l; steps_l. force_l false. force_l (Vundef↑). 
    destruct _q1. s. iDestruct "ASM" as "[[% [[% [% #I]] [TKN P]]] _]". hss.
    iInv "I" as "INV" "ACC". iEval (SL_red) in "INV".
    iDestruct "INV" as "[PT | [PT [R' TKN']]]"; cycle 1.
    { SL_red. iCombine "TKN" "TKN'" gives %WF; inv WF. }
    steps_r; inline_r; steps_r.
    force_r (_,_,_,_). forces_r.
    iSplitL "PT".
    { iFrame. et. }
    steps_r. iDestruct "GRT" as "[[↦ %] %]"; hss.
    iMod ("ACC" with "[↦ TKN P]") as "_".
    { SL_red. iRight. iFrame. }
    steps_r. forces_l. iSplit; et.
    steps_l. sch_yield_rr. sch_yield_l.
    step. et.
  Unshelve. all: eauto.
  (*SLOW*)Qed.

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
      (SpinLockA.t ★ MemA.t, emp%I)
      (SpinLockI.t ★ MemA.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End LockIA. End LockIA.
