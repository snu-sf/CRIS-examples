Require Import CRIS.

Require Import ImpPrelude.
Require Import SpinLockMainHeader SpinLockMainI SpinLockMainA.
Require Import SpinLockHeader SpinLockI SpinLockA SchHeader SchA MemA SchTactics.
From iris Require Import frac_auth numbers.

Module SpinLockMainIA. Section SpinLockMainIA.
  Import SpinLockAS SpinLockMainAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!memGΓ Γ, !SchAGΣ Σ, !SchAGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Context (u_a : univ_id). (* univ_id of the source/mem module *)
  Context (sp_s sp_user_s sp_mem : string → option fspec). (* sps of lock/sch/mem *)
  Context (SchInSp : sp_incl (SchAS.sp u_a sp_user_s) sp_s).
  Context (MemInSp : sp_incl MemA.sp sp_s).
  Context (MainInSp : sp_incl (SpinLockMainAS.sp u_a) sp_user_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition MemA := (MemA.t u_a sp_mem).
  Local Definition SpinLockA := (SpinLockA.t u_a sp_s).
  Local Definition SpinLockMainA := (SpinLockMainA.t u_a sp_s).
  Local Definition SpinLockMainI := (SpinLockMainI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockMainA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (SpinLockMainA ★ (MemA ★ SpinLockA)).
  Local Definition MI := (SpinLockMainI ★ (MemA ★ SpinLockA)).

  Lemma incr_simF : HSim.sim_fun open MA MI IstFull SpinLockMainHdr.incr.
  Proof.
    init_simF u_a 0.
    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[[-> [TID [%γ_l [#I F]]]] ->]". hss.
    rename q2 into γ_v, q4 into ofs_v, q6 into blk_v, q8 into ofs_l, q10 into blk_l, q9 into tid.
    (* main code *)
    steps_l. hss. steps_l. rewrite /SpinLockMainA.incr. steps_l.
    steps_r. hss. steps_r. rewrite /SpinLockMainI.incr. steps_r.
    unfold_iter_l. steps_l.
    (* tgt yields *)
    sch_yield_r; iFrame.
    clear st_src st_tgt NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST TID".
    steps_r. sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* tgt inline - lock acquire *)
    inline_r. force_r (tid, γ_l, Vptr blk_l ofs_l, existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    steps_r. forces_r. iFrame.
    iSplit; eauto. hss. steps_r.
    sch_yield_l. force_l false. steps_l.
    (* start coinduction for lock acquisition *)
    iApply wsim_reset. iStopProof.
    revert nths. combine_quant NODS. combine_quant NODD. combine_quant st_s. combine_quant st_t.
    eapply wsim_coind.
    iIntros (g' [st_t [st_s [nths [NODS NODD]]]]) "[#I [F IST]] _ #CIH".
    unfold_iter_r. unfold_iter_l. steps_l. steps_r.
    (* tgt yield *)
    sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST".
    steps_r. destruct q; cycle 1.
    { (* fail case *)
      steps_r. sch_yield_l. force_l false. steps_l. by_coind "CIH".
      hss. iFrame. eauto.
    }
    (* success case *)
    steps_r. iDestruct "GRT" as "[[_ [TKN P]] <-]". hss. steps_r.
    (* tgt yield *)
    sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST TID".
    rewrite /lock_P; SL_red; iDestruct "P" as "[TKN [%x P]]"; SL_red; iDestruct "P" as "[PT P]".
    (* tgt inline - mem load *)
    inline_r. force_r (blk_v, ofs_v, Vint x, 1%Qp). forces_r. iSplitL "PT"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* tgt yield *)
    sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST TID".
    sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* tgt inline - mem store *)
    inline_r. force_r (blk_v, ofs_v, Vint (x + 1)). forces_r. iSplitL "PT"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST TID".
    iCombine "P F" as "C". iMod (own_update with "C") as "[F C]".
    { apply frac_auth_update, (Z_local_update _ _ (x + 1) 1); lia. }
    (* tgt inline - lock acquire - restore lock protected proposition *)
    inline_r. force_r (tid, γ_l, Vptr blk_l ofs_l, existT 0 (lock_P (blk_v, ofs_v) γ_v)).
    forces_r.
    iSplitL "TID F PT TKN".
    { SL_red. rewrite /lock_P; ss. iSplit; iFrame; eauto. iSplit; eauto. iSplit.
      { iExact "I". }
      { iExists _; SL_red; iFrame. }
    }
    steps_r. hss. steps_r.
    (* tgt yield *)
    sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST".
    steps_r. iDestruct "GRT" as "[[-> TID] _]". hss. steps_r.
    sch_yield_r; iFrame.
    clear st_s st_t NODS NODD nths; iIntros (nths st_s st_t NODS NODD) "IST TID". steps_r.
    (* src yield *)
    sch_yield_l. steps_l. force_l true. steps_l. forces_l. iFrame; iSplit; eauto.
    (* both terminate *)
    steps_l. step. iFrame. eauto.
    Unshelve. all: eauto.
  (*FAST*)Qed.

  Ltac reintro nths :=
    match goal with
    | NODS : List.NoDup (map fst ?st_s), NODD : List.NoDup (map fst ?st_t) |- ?a
      => clear nths NODS st_s NODD st_t; iIntros (nths st_s st_t NODS NODD) end.

  Lemma main_simF : HSim.sim_fun open MA MI IstFull SpinLockMainHdr.main.
  Proof.
    init_simF u_a 0.
    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[[-> TID] ->]". hss.
    (* tgt yield *)
    steps_r. sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    (* tgt inline - mem alloc - counter allocation *)
    inline_r. force_r 1. forces_r. iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[%blk [-> [GRT _]]] ->]". hss. steps_r.
    steps_r. sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    (* tgt inline - mem store - counter initialization *)
    inline_r. force_r (blk, 0%Z, Vint 0). forces_r. iFrame; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    steps_r. sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    (* create lock-guarded proposition *)
    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { eapply frac_auth_valid; ss. }
    iIntros "[%γ [B W]]".
    (* tgt inline - newlock *)
    inline_r. force_r (0, existT 0 (lock_P (blk, 0%Z) γ)). forces_r. iSplitL "TID B PT"; eauto.
    { SL_red; iSplit; eauto. iFrame. iExists _; SL_red; iFrame. }
    steps_r. hss. steps_r.
    (* src/tgt yields *)
    sch_yield_r. iFrame; reintro nths. iIntros "IST".
    steps_r. iDestruct "GRT" as "[[TID [%val [%γ_l [-> #I]]]] %EQ]". hss. steps_r.
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    iPoseProof "I" as "[%b_l [%o_l [-> _]]]".
    sch_yield_l. steps_l. force_l (Vptr b_l o_l, Vptr blk 0). steps_l. sch_yield_l.
    (* create preconditions of incr *)
    iDestruct "W" as "[W1 W2]".
    (* spawn thread 1 - incr *)
    steps_l. sch_spawn.
    { apply MainInSp; ss. }
    { eapply (incr_spawnable). }
    iFrame; ss; clear nths st_src st_tgt NODS NODD.
    iSplit.
    { iSplit; eauto. }
    iIntros (tid nths st_s st_t NODS NODD) "IST TID TKN".
    steps_l. steps_r.
    (* src/tgt yields *)
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    sch_yield_l. steps_l.
    (* spawn thread 2 - incr *)
    sch_spawn.
    { apply MainInSp; ss. }
    { eapply (incr_spawnable u_a). }
    iSplitL "IST"; ss; clear nths st_s st_t NODS NODD. iFrame.
    iSplit.
    { iSplit; eauto. }
    iIntros (tid2 nths st_s st_t NODS NODD) "IST TID TKN2".
    steps_l. steps_r.
    (* src/tgt yields *)
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    sch_yield_l. steps_l.
    (* join thread 1 - incr *)
    sch_join; iFrame.
    clear nths st_s st_t NODS NODD; iIntros (nths st_s st_t vret ret NODS NODD) "IST TID W1 /=".
    steps_r. sch_yield_r.
    iFrame; ss; clear nths st_s st_t NODS NODD; iIntros (nths st_s st_t NODS NODD) "IST TID".
    sch_yield_l. steps_l.
    (* join thread 2 - incr *)
    sch_join; iFrame.
    clear nths st_s st_t NODS NODD; iIntros (nths st_s st_t vret2 ret2 NODS NODD) "IST TID W2 /=".
    steps_l. steps_r.
    unfold_iter_l. steps_l.
    sch_yield_r.
    iFrame; ss; clear nths st_s st_t NODS NODD; iIntros (nths st_s st_t NODS NODD) "IST TID".
    sch_yield_l. force_l false. steps_l.
    (* tgt inline - lock acquire *)
    inline_r. force_r (0, γ_l, Vptr b_l o_l, existT 0 (lock_P (blk, 0%Z) γ)). forces_r. iFrame.
    iSplit; eauto.
    steps_r. hss. steps_r.
    (* start coinduction for lock acquisition *)
    iApply wsim_reset. iStopProof.
    revert nths. combine_quant NODS. combine_quant NODD. combine_quant st_s. combine_quant st_t.
    eapply wsim_coind.
    iIntros (g' [st_t [st_s [nths [NODS NODD]]]]) "[#I [W1 [W2 IST]]] _ #CIH /=".
    unfold_iter_r. unfold_iter_l. steps_r.
    (* tgt yield *)
    sch_yield_r.
    iSplitL "IST"; ss; clear nths st_s st_t NODS NODD; iIntros (nths st_s st_t NODS NODD) "IST".
    steps_r. destruct q; cycle 1.
    { (* fail case *)
      steps_r. sch_yield_l. force_l false. steps_l.
  iApply wsim_progress. iApply wsim_base_t.
  iSpecialize ("CIH" $! _).
  (hrepeat do 1 unshelve first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); [..|s; grind; iIntrosFresh "I"; iApply "CIH"]; try eassumption.


      hss. iFrame. eauto.
    }
    (* success case *)
    steps_r. iDestruct "GRT" as "[[-> [TID [TKN P]]] _]". hss. steps_r.
    SL_red. iCombine "W1 W2" as "W". iDestruct "P" as "[%x P]"; SL_red; iDestruct "P" as "[PT B]".
    iCombine "B W" gives %WF%frac_auth_agree. inv WF.
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    (* tgt inline - mem load *)
    inline_r. force_r (blk, 0%Z, Vint 2%Z, 1%Qp). forces_r. iSplitL "PT"; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* tgt yield *)
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    (* tgt inline - lock release *)
    inline_r. force_r (0, γ_l, Vptr b_l o_l, existT 0 (lock_P (blk, 0%Z) γ)). forces_r.
    iSplitL "TKN TID B PT".
    { SL_red. iSplit; eauto. iFrame. iSplit; eauto. iSplit; eauto. iExists _; SL_red; iFrame. }
    steps_r. hss. steps_r.
    (* tgt yield *)
    sch_yield_r. iFrame; reintro nths. iIntros "IST".
    steps_r. iDestruct "GRT" as "[[-> TID] _]". hss. steps_r.
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID".
    sch_yield_l. force_l true. steps_l.
    (* both output - counter value *)
    sch_yield_l. step.
    steps_l. steps_r.
    sch_yield_r. iFrame; reintro nths. iIntros "IST TID". steps_r.
    sch_yield_l. steps_l. forces_l. iSplit; eauto. steps_l.
    (* terminate both *)
    step. iSplit; eauto.
  Unshelve. all:eauto.
  (*FAST*)Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; iSplit; eauto. }
    { eapply main_simF. }
    { eapply incr_simF. }
  Qed.
End SpinLockMainIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !SpinLockMainAGΓ Γ, !SpinLockAGΓ Γ}.

  Definition ctxr (u : univ_id) (sp_s sp_user_s sp_mem : string → option fspec)
      (SchInSp : sp_incl (SchAS.sp u sp_user_s) sp_s)
      (MainInSp : sp_incl (SpinLockMainAS.sp u) sp_user_s)
      (MemInSp : sp_incl MemA.sp sp_s) :
    ctx_refines
      ((SpinLockMainA.t u sp_s) ★ (MemA.t u sp_mem ★ (SpinLockA.t u sp_s)), emp%I)
      ((SpinLockMainI.t)         ★ (MemA.t u sp_mem ★ (SpinLockA.t u sp_s)), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End SpinLockMainIA.
