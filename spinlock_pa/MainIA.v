Require Import CRIS.
From CRIS.spinlock_pa Require Import Header MainI MainA LockI LockA.
Require Import ImpPrelude.
Require Import SchHeader SchA MemA SchTactics.
From iris Require Import frac_auth numbers.

Module MainIA. Section MainIA.
  Import LockAS MainAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_spinlockG: !spinlockG}.
  Context `{_spinlockmainG: !spinlockmainG}.

  Context (E : coPset) (q: Qp).
  Context (sp_s: sp_type). (* sps of lock/sch/mem *)
  Context (sp_user_s: spl_type).
  Context (LockInE: ↑N_SpinLockA ⊆ E).  
  Context (SchInSp_s : sp_incl (SchAS.sp sp_user_s E q) sp_s).
  Context (MainInSp : spl_sub (MainAS.sp E q) sp_user_s).

  Local Definition MemP := MemP.t.
  Local Definition SpinLockA := SpinLockA.t.
  Local Definition SpinLockMainA := (SpinLockMainA.t E q sp_s).
  Local Definition SpinLockMainI := (SpinLockMainI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockMainA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockMainA ★ (SpinLockA E ★ MemP)).
  Local Notation MI := (SpinLockMainI ★ (SpinLockA E ★ MemP)).

  Definition init_cond := MainAS.init_cond E q.

  Lemma incr_simF :
    ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockMainHdr.incr).
  Proof using LockInE SchInSp_s MainInSp.
    init_simF.
    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[TID [-> [-> [%γ_l [#I F]]]]]". hss.
    destruct _q5 as [blk_l ofs_l], _q6 as [blk_v ofs_v].
    rename _q4 into γ_v, _q1 into tid.
    (* main code *)
    steps_l. hss. steps_l. rewrite /SpinLockMainA.incr. steps_l.
    steps_r. hss. steps_r. rewrite /SpinLockMainI.incr. steps_r.
    sch_yield_ir. steps_r.

    (* tgt inline - lock acquire *)
    sch_yield_ir. steps_r.
    inline_r. steps_r.
    lat_real_ir "IST TID".
    { iFrame. instantiate (1:= (_,_,existT _ _)); s.
      iModIntro. iSplit; et.
      iIntros "[W [% [% _]]]". hss.
    }
    steps_r. ru_r. iIntros (?) "SIM". unfold_pre_post.
    iApply wsim_unfold; iIntros "W".
    iMod ("SIM" $! (_,_,existT _ _) with "[W]") as "[PR [W2 [_ [-> [TKN P]]]]]".
    { iFrame "I". iFrame. et. }
    do 2 rewrite sl_red. iDestruct "P" as "(%x & PT & P)".
    iApply wsim_fold; iFrame.
    forces_r; iFrame.
    steps_r. sch_yield_ir. steps_r. hss. steps_r. sch_yield_ir.

    (* tgt inline - mem load *)
    steps_r. inline_r. steps_r. unfold_lat_real_r.
    force_r (blk_v, ofs_v, 1%Qp, Vint x).
    iSplitL "PT"; iFrame; et.
    iIntros "[_ [PT ->]]". steps_r. hss. steps_r.
    sch_yield_ir. steps_r. sch_yield_ir. steps_r.

    (* tgt inline - mem store *)
    steps_r. inline_r. steps_r. unfold_lat_real_r.
    force_r (blk_v, ofs_v, _, Vint (x + 1)).
    iSplitL "PT"; iFrame; et.
    iIntros "[_ [PT ->]]". steps_r. hss. steps_r.
    sch_yield_ir. steps_r.

    iCombine "P F" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }

    (* tgt inline - lock acquire - restore lock protected proposition *)
    steps_r. inline_r. steps_r. unfold_lat_real_r.
    sch_yield_ir. steps_r.
    iApply wsim_unfold; iIntros "W".
    force_r (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    iSplitL "W F PT TKN".
    { rewrite /lock_P; ss.
      iFrame "I". iFrame. repeat (iSplit; et). 
      do 2 rewrite sl_red. iFrame.
    }
    s. iIntros "[W %]"; des; subst.
    iApply wsim_fold; iFrame.
    
    steps_r. sch_yield_ir. steps_r. hss. steps_r. sch_yield_ir. steps_r.
    sch_yield_l. steps_l.
    iApply wsim_unfold; iIntros "W".
    forces_l. iFrame. iSplit; et.
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
    steps_l. steps_r. sch_yield_ir.

    (* tgt inline - mem alloc - counter allocation *)
    steps_r. inline_r. steps_r. unfold_lat_real_r.
    force_r 1. iSplit; eauto.
    iIntros "[_ [%blk [-> [GRT _]]]]". steps_r. hss. steps_r. sch_yield_ir.

    (* tgt inline - mem store - counter initialization *)
    steps_r. inline_r. steps_r. unfold_lat_real_r.
    force_r (blk, 0%Z, _, Vint 0). s.
    iFrame; iSplit; eauto.
    iIntros "[_ [PT ->]]". steps_r. hss. steps_r. sch_yield_ir.

    (* create lock-guarded proposition *)
    iMod (own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)) as "(%γ & B & W)".
    { eapply frac_auth_valid; ss. }

    (* tgt inline - newlock *)
    steps_r. inline_r. steps_r. unfold_lat_real_r. sch_yield_ir. steps_r.
    iApply wsim_unfold. iIntros "I".
    force_r (existT 0 (lock_P (blk, 0%Z) γ)).
    iSplitL "B I PT"; eauto.
    { iFrame. s. rewrite sl_red; iSplit; eauto. iSplit; et. iFrame. }
    iIntros "[WINV [%EQ [%v [%γ_l [-> #I]]]]]". hss.
    iApply wsim_fold; iFrame.
    steps_r. sch_yield_ir. steps_r. hss. steps_r. sch_yield_ir.
    sch_yield_l. steps_l. force_l (v, Vptr (blk, 0%Z)).
    steps_l. sch_yield_l.

    iPoseProof "I" as "[%bofs [-> _]]".
    iDestruct "W" as "[W1 W2]".

    (* spawn thread 1 - incr *)
    steps_l. steps_r. force_l (_,_,_). forces_l. iSplitL "W1 TID".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame; et.
    }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [TID [% [[-> ->] TKN1]]]]]".
    rename _q0 into tid1. steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* spawn thread 2 - incr *)
    steps_l. steps_r. force_l (_,_,_). forces_l. iSplitL "W2 TID".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame; et.
    }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [TID [% [[-> ->] TKN2]]]]]".
    rename _q0 into tid2. steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 1 - incr *)
    steps_l. steps_r.  force_l (_,_,_). forces_l. iSplitL "TID TKN1".
    { iExists _. do 2 (iSplit; et). iFrame. }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W1]]]]]]".
    rename _q1 into vret1. steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 2 - incr *)
    steps_l. steps_r.  force_l (_,_,_). forces_l. iSplitL "TID TKN2".
    { iExists _. do 2 (iSplit; et). iFrame. }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W2]]]]]]".
    rename _q1 into vret2. steps_r. hss. steps_r.
    sch_yield_ir.

    (* tgt inline - lock acquire *)
    steps_r. inline_r. steps_r.
    lat_real_ir "IST TID".
    { instantiate (1:= (_,_,existT _ _)). s.
      iFrame. iModIntro. iSplit; et.
      iIntros "[W _]"; et.
    }
    iApply wsim_unfold; iIntros "WINV".
    steps_r. force_r (γ_l, Vptr bofs, existT 0 (lock_P (blk, 0%Z) γ)). s.
    iFrame. iSplit; eauto.
    iIntros "[WINV [_ [% [TKN P]]]]"; hss.
    do 3 rewrite sl_red. iCombine "W1 W2" as "W".
    iDestruct "P" as "(%x & PT & B)".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.
    iApply wsim_fold; iFrame.
    steps_r. sch_yield_ir. steps_r. hss. steps_r. sch_yield_ir.
    
    (* tgt inline - mem load *)
    steps_r. inline_r. steps_r. unfold_lat_real_r.
    force_r (blk, 0%Z, 1%Qp, Vint 2%Z); s.
    iSplitL "PT"; eauto. iIntros "[_ [PT ->]]".
    steps_r. hss. steps_r. sch_yield_ir. steps_r. sch_yield_ir.
    
    (* tgt inline - lock release *)
    steps_r. inline_r. steps_r.
    unfold_lat_real_r. sch_yield_ir. steps_r.
    iApply wsim_unfold; iIntros "WINV".
    force_r (γ_l, Vptr bofs, existT 0 (lock_P (blk, 0%Z) γ)). s.
    iSplitL "WINV TKN B PT".
    { iFrame. do 2 rewrite sl_red. repeat (iSplit; et; iFrame). }
    iIntros "[WINV [_ ->]]".
    iApply wsim_fold; iFrame.
    steps_r. sch_yield_ir. steps_r. hss. steps_r. sch_yield_ir.

    (* both output - counter value *)
    sch_yield_l. step. steps_l. steps_r. sch_yield_ir. sch_yield_l.

    (* terminate both *)
    step. et.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { eapply main_simF. }
    { eapply incr_simF. }
  Qed.

  Definition ctxr :
  ctx_refines
  ((SpinLockMainA.t E q sp_s) ★ ((SpinLockA.t E) ★ MemP.t), init_cond)
  ((SpinLockMainI.t)          ★ ((SpinLockA.t E) ★ MemP.t), emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End MainIA. End MainIA.
