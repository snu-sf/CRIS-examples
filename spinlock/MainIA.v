Require Import CRIS.
From CRIS.spinlock Require Import Header MainI MainA LockI LockA.
Require Import ImpPrelude.
Require Import SchHeader SchA MemA SchTactics.
From iris Require Import frac_auth numbers.

Module MainIA. Section MainIA.
  Import LockAS MainAS.
  Context `{CrisG: !crisG Γ Σ α β τ _S _I}.
  Context `{MemG: !memG}.
  Context `{Schg: !schG}.
  Context `{SpinlockG: !spinlockG}.
  Context `{SpinlockmainG: !spinlockmainG}.

  Context (E : coPset) (q: Qp).
  Context (sp_s: sp_type). (* sps of lock/sch/mem *)
  Context (sp_user_s: spl_type).
  Context (LockInE: ↑N_SpinLockA ⊆ E).
  Context (SchInSp_s : sp_incl (SchAS.sp sp_user_s E q) sp_s).
  Context (MainInSp : spl_sub (MainAS.sp E q) sp_user_s).

  Local Definition MemA := MemA.t.
  Local Definition SpinLockA := SpinLockA.t.
  Local Definition SpinLockMainA := (SpinLockMainA.t E q sp_s).
  Local Definition SpinLockMainI := (SpinLockMainI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockMainA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockMainA ★ (SpinLockA ★ MemA)).
  Local Notation MI := (SpinLockMainI ★ (SpinLockA ★ MemA)).

  Definition init_cond := MainAS.init_cond E q.

  Lemma incr_simF :
    ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockMainHdr.incr).
  Proof using LockInE SchInSp_s MainInSp.
    init_simF.
    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[TID [[-> [%γ_l [#I F]]] ->]]". hss.
    destruct _q5 as [blk_l ofs_l], _q6 as [blk_v ofs_v].
    rename _q4 into γ_v, _q1 into tid.

    (* main code *)
    steps_l. hss. steps_l. rewrite /SpinLockMainA.incr. steps_l.
    steps_r. hss. steps_r. rewrite /SpinLockMainI.incr. steps_r.
    sch_yield_ir. steps_r.

    (* tgt inline - lock acquire *)
    sch_yield_ir. steps_r. inline_r. steps_r.
    iApply wsim_reset. iStopProof.
    revert st_tgt. combine_quant st_src. eapply wsim_coind.
    intros g _ CIH [st_src st_tgt]. destruct_quant CIH; s.
    iIntros "[#L [F [IST TID]]]".

    unfold_iter_r. steps_r. sch_yield_ir. steps_r.
    force_r (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    force_r. iFrame "L". iSplit; eauto.
    steps_r. destruct _q; [|clear CIH].
    { steps_r. by_coind CIH. hss_copset. iFrame "L". iFrame. }
    steps_r. iDestruct "GRT" as "[[% [TKN P]] _]". hss.
    sch_yield_ir. steps_r. hss. steps_r.
    rewrite /lock_P; SL_red; iDestruct "P" as "[%x P]".
    SL_red; iDestruct "P" as "[PT P]".

    (* tgt inline - mem load *)
    sch_yield_ir. steps_r. inline_r. force_r (blk_v, ofs_v, 1%Qp, Vint x).
    forces_r. iFrame "PT". iSplit; et.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    sch_yield_ir. steps_r. sch_yield_ir.

    (* tgt inline - mem store *)
    steps_r. inline_r. steps_r. force_r (blk_v, ofs_v, _, Vint (x + 1)).
    forces_r. iFrame "PT". iSplit; et.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    sch_yield_ir.
    
    (* tgt inline - lock release *)
    steps_r. inline_r. steps_r. unfold_iter_r. steps_r. sch_yield_ir.
    iCombine "P F" as "C". iMod (own_update with "C") as "[F P]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    force_r (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    forces_r. SL_red. iFrame "L". iFrame. iSplitL "F PT".
    { repeat (iSplit; et). iExists _. SL_red. iFrame. }
    steps_r. iDestruct "GRT" as "%"; hss.
    sch_yield_ir. steps_r. hss. steps_r.

    (* prove src postcondition *)
    sch_yield_ir. steps_r.
    sch_yield_l. steps_l.
    forces_l. iFrame. iSplit; et.

    (* prove IST *)
    step. et.
  (*SLOW*)Qed.

  Lemma main_simF :
    ISim.sim_fun open MA MI init_cond IstFull None.
  Proof using LockInE SchInSp_s MainInSp.
    init_simF.
    rewrite /Sch.spawn /Sch.join.

    (* establish IST *)
    iClear "IST".
    iAssert (IstFull [] []) as "IST".
    { do 4 (iExists []). iPureIntro. esplits; et; ss. }
    iRevert "IST"; iIntros "IST"; rewrite bi.intuitionistically_elim.

    steps_l. steps_r.
    sch_yield_ir.

    (* tgt inline - mem alloc - counter allocation *)
    steps_r. inline_r. steps_r. force_r 1.
    forces_r. iSplit; et.
    steps_r. iDestruct "GRT" as "[[%blk [-> [GRT _]]] ->]".
    hss. steps_r. sch_yield_ir.

    (* tgt inline - mem store - counter initialization *)
    steps_r. inline_r. steps_r. force_r (blk, 0%Z, _, Vint 0).
    forces_r. iFrame; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]".
    hss. steps_r. sch_yield_ir.
    
    (* create lock-guarded proposition *)
    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { eapply frac_auth_valid; ss. }
    iIntros "[%γ [B W]]".

    (* tgt inline - newlock *)
    steps_r. inline_r. steps_r. unfold_iter_r. sch_yield_ir.
    force_r (existT 0 (lock_P (blk, 0%Z) γ)). forces_r.
    iSplitL "B PT"; eauto.
    { repeat (iSplit; et). SL_red. iExists _. SL_red. iFrame. }
    steps_r. iDestruct "GRT" as "[[%v [%γ_l [-> [% [% #I]]]]] _]". hss.
    sch_yield_ir. steps_r. hss. steps_r. sch_yield_ir.
    iDestruct "W" as "[W1 W2]".

    (* spawn thread 1 - incr *)
    sch_yield_l. force_l (_,_). steps_l. sch_yield_l.
    steps_l. force_l (_,_,_). forces_l. iSplitL "W1 TID".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame. repeat (iSplit; et). iExists _, _. iFrame "I". et.
    }
    steps_l. steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [TID [% [[-> ->] TKN1]]]]]". hss.
    rename _q0 into tid1. steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* spawn thread 2 - incr *)
    steps_l. force_l (_,_,_). forces_l. iSplitL "W2 TID".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame. repeat (iSplit; et). iExists _, _. iFrame "I". et.
    }
    steps_l. steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [TID [% [[-> ->] TKN2]]]]]". hss.
    rename _q0 into tid2.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 1 - incr *)
    steps_l. force_l (_,_,_). forces_l. iSplitL "TID TKN1".
    { iExists _. do 2 (iSplit; et). iFrame. }
    steps_l. steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W1]]]]]]". hss.
    rename _q1 into vret.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 2 - incr *)
    steps_l. force_l (_,_,_). forces_l. iSplitL "TID TKN2".
    { iExists _. do 2 (iSplit; et). iFrame. }
    steps_l. steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W2]]]]]]". hss.
    rename _q1 into vret0.
    steps_r. hss. steps_r.
    sch_yield_ir.

    (* tgt inline - lock acquire *)
    steps_r. inline_r. steps_r.
    iApply wsim_reset. iStopProof.
    revert st_tgt. combine_quant st_src. eapply wsim_coind.
    intros g _ CIH [st_src st_tgt]. destruct_quant CIH; s.
    iIntros "[#I [W1 [W2 [IST TID]]]]".

    unfold_iter_r. steps_r. sch_yield_ir.
    force_r (γ_l, Vptr bofs, existT 0 (lock_P (blk, 0%Z) γ)). forces_r.
    iFrame "I". iSplit; eauto.
    steps_r. destruct _q.
    { steps_r. hss. by_coind CIH. iFrame "I". iFrame. }
    steps_r. iDestruct "GRT" as "[[-> [TKN P]] _]". hss.
    sch_yield_ir. steps_r. hss. steps_r. sch_yield_ir.

    SL_red. iCombine "W1 W2" as "W".
    iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT B]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.
    
    (* tgt inline - mem load *)
    steps_r. inline_r. steps_r. force_r (blk, 0%Z, 1%Qp, Vint 2%Z); s.
    forces_r. iSplitL "PT"; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss.
    steps_r. sch_yield_ir. steps_r. sch_yield_ir.

    (* tgt inline - lock release *)
    steps_r. inline_r. steps_r. unfold_iter_r. steps_r. sch_yield_ir.
    force_r (γ_l, Vptr bofs, existT 0 (lock_P (blk, 0%Z) γ)). forces_r.
    iSplitL "TKN B PT".
    { repeat (iSplit; et); SL_red; iFrame.
      - iExists _. iFrame "I". et.
      - iExists _. SL_red. iFrame.
    }
    steps_r. iDestruct "GRT" as "%"; des; hss.
    sch_yield_ir. steps_r. hss. steps_r.

    (* both output - counter value *)
    sch_yield_ir. sch_yield_l. step. steps_l. steps_r.
    (* both terminate *)
    sch_yield_ir. sch_yield_l. step. et.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { eapply main_simF. }
    { eapply incr_simF. }
  Qed.

  Definition ctxr :
  ctx_refines
  ((SpinLockMainA.t E q sp_s) ★ (SpinLockA.t ★ MemA.t), init_cond)
  ((SpinLockMainI.t)          ★ (SpinLockA.t ★ MemA.t), emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End MainIA. End MainIA.
