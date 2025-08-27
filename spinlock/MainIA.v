Require Import CRIS.
From CRIS.spinlock Require Import Header MainI MainA LockI LockA.
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
  Context (sp_s sp_t: sp_type). (* sps of lock/sch/mem *)
  Context (sp_user_s sp_user_t: spl_type).
  Context (SchInSp_s : sp_incl (SchAS.sp sp_user_s E q) sp_s).
  Context (SchInSp_t : sp_incl (SchAS.sp sp_user_t E (q / 2)) sp_t).
  Context (MainInSp : spl_sub (MainAS.sp E q) sp_user_s).

  Local Definition MemP := MemP.t.
  Local Definition SpinLockA := (SpinLockA.t E (q / 2) sp_t).
  Local Definition SpinLockMainA := (SpinLockMainA.t E q sp_s).
  Local Definition SpinLockMainI := (SpinLockMainI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockMainA.(Mod.scopes) IstTrue) IstEq).
  Local Notation MA := (SpinLockMainA ★ (SpinLockA ★ MemP)).
  Local Notation MI := (SpinLockMainI ★ (SpinLockA ★ MemP)).

  Definition init_cond := MainAS.init_cond E q.

  Lemma incr_simF :
    ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockMainHdr.incr).
  Proof using SchInSp_s SchInSp_t MainInSp.
    init_simF.
    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[TID [[-> [%γ_l [#I F]]] ->]]". hss.
    destruct _q5 as [blk_l ofs_l], _q6 as [blk_v ofs_v].
    rename _q4 into γ_v, _q1 into tid.
    (* main code *)
    steps_l. hss. steps_l. rewrite /SpinLockMainA.incr. steps_l.
    steps_r. hss. steps_r. rewrite /SpinLockMainI.incr. steps_r.
    (* tgt yields *)
    sch_yield_ir.
    steps_r.
    (* tgt inline - lock acquire *)
    sch_yield_ir.
    steps_r. inline_r. force_r (tid, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))).
    steps_r. forces_r.
    rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]".
    iFrame. iSplit; eauto. hss. steps_r.
    sch_yield_ii; [erewrite Qp.div_2; et|].

    (* (* success case *) *)
    steps_r. iDestruct "GRT" as "[TID' [[-> [TKN P]] _]]". hss. steps_r.
    iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2.
    (* tgt yield *)
    sch_yield_ir.
    rewrite /lock_P; SL_red; iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT P]".
    (* tgt inline - mem load *)
    steps_r. inline_r. steps_r.
    unfold_real_lat_r. force_r (blk_v, ofs_v, 1%Qp, Vint x).
    iSplitL "PT"; iFrame; eauto.
    iIntros "[PT %]". hss. steps_r. hss_r; steps_r.
    (* tgt yield *)
    do 2 (sch_yield_ir).
    (* tgt inline - mem store *)
    steps_r. inline_r. steps_r.
    unfold_real_lat_r. force_r (blk_v, ofs_v, _, Vint (x + 1)).
    iSplitL "PT"; iFrame; et.
    iIntros "[PT %]". steps_r. hss_r; steps_r.
    sch_yield_ir.
    iCombine "P F" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    (* tgt inline - lock acquire - restore lock protected proposition *)
    steps_r. inline_r. steps_r. force_r (tid, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))).
    rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]".
    forces_r. iSplitL "TID1 F PT TKN".
    { SL_red. rewrite /lock_P; ss.
      iFrame "TID1". iSplit; iFrame; eauto. iSplit; eauto. iSplit.
      { iExact "I". }
      { iExists _; SL_red; iFrame. }
    }
    steps_r. hss. steps_r.
    (* tgt yield *)
    sch_yield_ii; [erewrite Qp.div_2; et|].
    steps_r. iDestruct "GRT" as "[TID' [-> _]]". hss. steps_r.
    iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2.
    sch_yield_ir.
    (* src yield *)
    sch_yield_l. steps_l. forces_l. iFrame; iSplit; eauto.
    (* both terminate *)
    step. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma main_simF :
    ISim.sim_fun open MA MI init_cond IstFull None.
  Proof using SchInSp_s SchInSp_t MainInSp.
    init_simF.
    rewrite /Sch.spawn /Sch.join.

    (* establish IST *)
    iClear "IST".
    iAssert (IstFull [] []) as "IST".
    { do 4 (iExists []). iPureIntro. esplits; et; ss. }
    iRevert "IST"; iIntros "IST"; rewrite bi.intuitionistically_elim.

    steps_l. steps_r.
    (* tgt yield *)
    sch_yield_ir.

    (* tgt inline - mem alloc - counter allocation *)
    steps_r. inline_r. steps_r.
    unfold_real_lat_r. force_r 1; iSplit; eauto.
    iIntros "[%blk [% [GRT _]]]"; hss. steps_r. hss_r; steps_r.
    sch_yield_ir.
    (* tgt inline - mem store - counter initialization *)
    steps_r. inline_r. steps_r.
    unfold_real_lat_r. force_r (blk, 0%Z, _, Vint 0).
    iFrame; iSplit; eauto.
    iIntros "[PT %]". steps_r. hss. steps_r.
    sch_yield_ir.
    (* create lock-guarded proposition *)
    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { eapply frac_auth_valid; ss. }
    iIntros "[%γ [B W]]".
    (* tgt inline - newlock *)
    steps_r. inline_r. steps_r.
    force_r (0, existT 0 (lock_P (blk, 0%Z) γ)). forces_r.
    rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]".
    iSplitL "TID1 B PT"; eauto.
    { iFrame; SL_red; iSplit; eauto. iFrame. iExists _; SL_red; iFrame. }
    steps_r. hss. steps_r.
    (* src/tgt yields *)
    sch_yield_ii; [erewrite Qp.div_2; et|].
    steps_r. iDestruct "GRT" as "[TID' [[%val [%γ_l [-> #I]]] %EQ]]".
    hss. steps_r.
    iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2.
    sch_yield_ir.
    iPoseProof "I" as "[%bofs_l [-> _]]".
    sch_yield_l. steps_l. force_l (Vptr bofs_l, Vptr (blk, 0%Z)). steps_l. sch_yield_l.
    (* create preconditions of incr *)
    iDestruct "W" as "[W1 W2]".

    (* spawn thread 1 - incr *)
    steps_l. steps_r. force_l (_,_,_). forces_l. iSplitL "W1 TID".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame; et.
    }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [TID [% [[-> ->] TKN1]]]]]".
    rename _q0 into tid1.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* spawn thread 2 - incr *)
    steps_l. steps_r. force_l (_,_,_). forces_l. iSplitL "W2 TID".
    { iExists (_,_). iSplit; et. iFrame. iExists _, _, _. iSplit.
      - iPureIntro; esplits; et. r; eauto using incr_spawnable.
      - iFrame; et.
    }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [TID [% [[-> ->] TKN2]]]]]". hss.
    rename _q0 into tid2.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 1 - incr *)
    steps_l. steps_r.  force_l (_,_,_). forces_l. iSplitL "TID TKN1".
    { iExists _. do 2 (iSplit; et). iFrame. }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W1]]]]]]".
    hss. rename _q1 into vret.
    steps_r. hss. steps_r.
    sch_yield_ir. sch_yield_l.

    (* join thread 2 - incr *)
    steps_l. steps_r.  force_l (_,_,_). forces_l. iSplitL "TID TKN2".
    { iExists _. do 2 (iSplit; et). iFrame. }
    call "IST".
    steps_l. iDestruct "ASM" as "[% [-> [% [% [[-> ->] [TID W2]]]]]]".
    hss. rename _q1 into vret0.
    steps_r. hss. steps_r.
    sch_yield_ir.

    (* tgt inline - lock acquire *)
    steps_r. inline_r. steps_r.
    force_r (_, (γ_l, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). forces_r.
    rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]".
    iFrame. iSplit; eauto.
    steps_r. hss. steps_r.
    sch_yield_ii; [erewrite Qp.div_2; et|].
    steps_r. iDestruct "GRT" as "[TID' [[-> [TKN P]] _]]". hss. steps_r.
    SL_red. iCombine "W1 W2" as "W".
    iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT B]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.
    iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2.
    sch_yield_ir.
    (* tgt inline - mem load *)
    steps_r. inline_r. steps_r.
    unfold_real_lat_r. force_r (blk, 0%Z, 1%Qp, Vint 2%Z); s.
    iFrame "PT". iSplit; et.
    iIntros "[PT %]". steps_r. hss. steps_r.
    (* tgt yield *)
    do 2 (sch_yield_ir).
    (* tgt inline - lock release *)
    steps_r. inline_r. steps_r.
    force_r (_, (γ_l, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). forces_r.
    rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]".
    iSplitL "TKN TID1 B PT".
    { iFrame; SL_red. iSplit; eauto. iFrame. iSplit; eauto. iSplit; eauto.
      iExists _; SL_red; iFrame.
    }
    steps_r. hss. steps_r.
    (* tgt yield *)
    sch_yield_ii; [erewrite Qp.div_2; et|].
    steps_r. iDestruct "GRT" as "[TID' [-> _]]". hss. steps_r.
    iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2.
    sch_yield_ir.
    (* both output - counter value *)
    sch_yield_l. step.
    steps_l. steps_r.
    sch_yield_ir.
    sch_yield_l. 
    (* terminate both *)
    step. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof.
    init_sim.
    { eapply main_simF. }
    { eapply incr_simF. }
  Qed.

  Definition ctxr :
    ctx_refines
    ((SpinLockMainA.t E q sp_s) ★ ((SpinLockA.t E (q/2) sp_t) ★ MemP.t), init_cond)
    ((SpinLockMainI.t)          ★ ((SpinLockA.t E (q/2) sp_t) ★ MemP.t), emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End MainIA. End MainIA.
