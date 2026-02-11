Require Import CRIS.
Require Import LockHeader MainI MainA LockI LockA.
Require Import ImpPrelude.
Require Import SchHeader SchA MemA SchTactics MemTactics.
From iris Require Import frac_auth numbers.

Module MainIA. Section MainIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !memGS, !schGS, !spinlockG, !spinlockmainG}.
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

  Lemma incr_simF : ISim.sim_fun open MA MI IstFull (Some SpinLockMainHdr.incr).
  Proof using SchInSp_s SchInSp_t MainInSp.
    iStartSim.
    (* process src precondition *)
    steps_l. destruct _q as [[stid mtid] [[[blk_l ofs_l] [blk_v ofs_v]] γ_v]]. rename _q0 into varg.
    iDestruct "ASM" as "[TID [-> [-> [%γ_l [#Lock Tkn]]]]]".
    hss_l; hss_r. steps_l; steps_r. hss_l; hss_r. steps_l; steps_r.

    (* main code *)
    rewrite /incr /SpinLockMainI.incr. steps_l. steps_r.
    (* tgt yields *)
    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    (* tgt inline - lock acquire *)
    steps_r. inline_r.
    force_r (_, _, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))).
    steps_r. forces_r.
    (* rewrite -{1}(Qp.div_2 q); iPoseProof (SchAS.tid_user_split with "TID") as "[TID1 ITD2]". *)
    iFrame "TID Lock". iSplit; eauto. steps_r. hss_r. steps_r.
    sch_yield_ii "IST".

    (* (* success case *) *)
    steps_r. iDestruct "GRT" as "[TID [<- [_ [TKN P]]]]". hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    (* tgt yield *)
    solve_base_sl_red. iDestruct "P" as "[%x [PT P]]".
    steps_r. load_r "PT". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    store_r "PT". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    iCombine "P Tkn" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    inline_r. steps_r.
    force_r (_, _, (γ_l, Vptr (blk_l, ofs_l), existT 0 (lock_P (blk_v, ofs_v) γ_v))). forces_r.
    iSplitL "TID F PT TKN".
    { solve_base_sl_red. iFrame. iSplit; eauto. }
    steps_r. hss_r; steps_r.
    sch_yield_ii "IST". steps_r.
    
    (* tgt inline - lock acquire - restore lock protected proposition *)
    iDestruct "GRT" as "[TID [<- _]]". hss_r. steps_r.
    (* iPoseProof (SchAS.tid_user_merge with "[TID TID']") as "TID"; iFrame; rewrite Qp.div_2. *)
    sch_yield_ir "IST" "TID".
    (* src yield *)
    sch_yield_l. steps_l. forces_l. iFrame; iSplit; eauto.
    (* both terminate *)
    step. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma main_simF : ISim.sim_fun open MA MI IstFull None.
  Proof using SchInSp_s SchInSp_t MainInSp.
    iStartSim. steps_l. destruct _q as [[stid mtid] []]. iDestruct "ASM" as "[TID ->]".

    rewrite /main. steps_l.
    steps_r. rewrite /SpinLockMainI.main. steps_r.
    rewrite /Sch.spawn.

    (* tgt yield *)
    sch_yield_ir "IST" "TID".

    (* tgt inline - mem alloc - counter allocation *)
    steps_r.
    iApply wsim_mem_alloc; ss. iIntros (blk) "[↦ _]". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    (* tgt inline - mem store - counter initialization *)
    steps_r.
    iApply (wsim_mem_store with "[↦]"); ss. iIntros"↦". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    (* create lock-guarded proposition *)
    iMod (own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)) as "[%γ [B W]]". { eapply frac_auth_valid; ss. }

    (* tgt inline - newlock *)
    steps_r. inline_r. force_r (stid, mtid, existT 0 (lock_P (blk, 0%Z) γ)). forces_r.
    iSplitL "TID B ↦"; eauto.
    { iFrame. solve_base_sl_red. iFrame. done. }
    steps_r. hss_r. steps_r.

    (* src/tgt yields *)
    sch_yield_ii "IST".
    steps_r. iDestruct "GRT" as "[TID [-> [%val [%γl [-> [%bofs_l [-> #Lock]]]]]]]".
    hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    (* iPoseProof "I" as "[%bofs_l [-> _]]". *)
    sch_yield_l. steps_l. force_l (Vptr bofs_l, Vptr (blk, 0%Z)). steps_l. sch_yield_l.
    (* create preconditions of incr *)
    iDestruct "W" as "[W1 W2]".

    (* spawn thread 1 - incr *)
    steps_l. simpl_sp. steps_r. force_l (_,_). forces_l. iSplitL "W1".
    { iExists _, _, _. iSplit; et. iSplitR.
      - iExists _; iSplit; [iPureIntro; simpl_sp|]; ss. iApply incr_spawnable.
      - iFrame "W1"; eauto. repeat iSplit; eauto. iExists _; iFrame "Lock"; auto.
    }
    call "IST". clear_st; iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[% [[-> ->] TKN1]]". 
    steps_r. hss_r. steps_r. hss_l. steps_l.
    sch_yield_ir "IST" "TID". sch_yield_l.

    (* spawn thread 2 - incr *)
    steps_l. simpl_sp. steps_r. force_l (_,_). forces_l. iSplitL "W2".
    { iExists _, _, _. iSplit; et. iSplitR.
      - iExists _; iSplit; [iPureIntro; simpl_sp|]; ss. iApply incr_spawnable.
      - iFrame "W2"; eauto. repeat iSplit; eauto. iExists _; iFrame "Lock"; auto.
    }
    call "IST". clear_st; iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[% [[-> ->] TKN2]]". 
    steps_r. hss_r. steps_r. hss_l. steps_l.
    sch_yield_ir "IST" "TID". sch_yield_l.

    (* join thread 1 - incr *)
    rewrite /Sch.join.
    steps_l. steps_r. simpl_sp. force_l (_,_,_). forces_l. iSplitL "TKN1 TID".
    { iFrame. eauto. }
    call "IST". clear_st; iIntros (ret st_src st_tgt) "IST".
    steps_l. steps_r. iDestruct "ASM" as "[TID [% [% [[-> ->] W1]]]]". solve_base_sl_red.
    hss_l; hss_r. steps_l; steps_r.
    sch_yield_ir "IST" "TID". sch_yield_l. steps_r. steps_l. simpl_sp.

    (* join thread 2 - incr *)
    force_l (stid, mtid, _). forces_l. iSplitL "TID TKN2".
    { iFrame; eauto. }
    call "IST". clear_st; iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[TID [% [% [[-> ->] W2]]]]". solve_base_sl_red. steps_r.
    hss_l; hss_r. steps_l; steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    (* tgt inline - lock acquire *)
    inline_r. steps_r.
    force_r (_, _, (γl, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). forces_r.
    iFrame "TID"; iSplitR.
    { repeat iSplit; eauto. iFrame "Lock"; auto. }
    steps_r. hss_r. steps_r.
    sch_yield_ii "IST". steps_r.
    iDestruct "GRT" as "[TID [<- [_ [TKN P]]]]". hss_r. steps_r.
    sch_yield_ir "IST" "TID". steps_r.
    iCombine "W1 W2" as "W". solve_base_sl_red.
    iDestruct "P" as "[%x [PT B]]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.

    (* tgt inline - mem load *)
    load_r "PT". steps_r. hss_r. steps_r.

    (* tgt yield *)
    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    (* tgt inline - lock release *)
    inline_r. steps_r.
    force_r (_, _, (γl, Vptr bofs_l, existT 0 (lock_P (blk, 0%Z) γ))). forces_r.
    iSplitL "TKN TID B PT".
    { solve_base_sl_red. iFrame. iFrame "Lock"; iSplit; eauto. }
    steps_r. hss_r. steps_r.

    (* tgt yield *)
    sch_yield_ii "IST". steps_r. iDestruct "GRT" as "[TID [<- _]]". hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    (* both output - counter value *)
    sch_yield_l. step.
    steps_l. steps_r.
    sch_yield_ir "IST" "TID". sch_yield_l.
    (* terminate both *)
    forces_l. iFrame; iSplit; first eauto. step. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { eapply main_simF. }
    { eapply incr_simF. }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.

  Definition ctxr :
    ctx_refines
      ((MainA.t N sp_s)  ★ ((LockA.t (↑N) sp_t) ★ MemA.t sp_s), emp%I)
      ((SpinLockMainI.t) ★ ((LockA.t (↑N) sp_t) ★ MemA.t sp_s), emp%I).
  Proof. eapply main_adequacy, sim. Qed.
End MainIA. End MainIA.
