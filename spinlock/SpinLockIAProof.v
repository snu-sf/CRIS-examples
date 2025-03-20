Require Import CRIS.

Require Import ImpPrelude.
Require Import SpinLockHeader SpinLockI SpinLockA MemA.
Require Import SchHeader SchA SchTactics.

Module SpinLockIA. Section SpinLockIA.
  Import SpinLockAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !SpinLockAGΓ Γ}.

  Context (u_a : univ_id). (* univ_id of the source/mem module *)
  Context (spc_s spc_user_s spc_mem : string → option fspec). (* spcs of lock/sch/mem *)
  Context (SchInSpc : spc_incl (SchAS.spc u_a spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.spc spc_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition MemA := (MemA.t u_a spc_mem).
  Local Definition SpinLockA := (SpinLockA.t u_a spc_s).
  Local Definition SpinLockI := (SpinLockI.t).
  Local Definition IstFull := (IstProd (IstSB SpinLockA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (SpinLockA ★ MemA).
  Local Definition MI := (SpinLockI ★ MemA).

  Lemma newlock_simF : HSim.sim_fun open MA MI IstFull SpinLockHdr.newlock.
  Proof.
    init_simF u_a 0.
    (* preprocess initial conditions *)
    steps_l. rename q1 into tid. destruct q2 as [n P]; s. iDestruct "ASM" as "[[TID P] ->]". hss.
    (* tgt yield *)
    steps_r. sch_yield_r. iFrame. clear nths NODS NODD; iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* tgt inline - mem alloc *)
    inline_r. force_r 1. forces_r. iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[%blk [-> [PT _]]] ->]". hss. steps_r.
    (* tgt yield *)
    sch_yield_r. iFrame. clear nths st_s st_t NODS NODD; iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* tgt inline - mem store *)
    inline_r. force_r (blk, 0%Z, Vint 0). steps_r. forces_r. iSplitL "PT"; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* src/tgt yield *)
    sch_yield_r. iFrame. clear nths st_s st_t NODS NODD; iIntros (nths st_s st_t NODS NODD) "IST TID".
    sch_yield_l. force_l (Vptr blk 0). steps_l. force_l. steps_l.
    (* prove source postcondition *)
    (* alloc invariant *)
    iApply (wsim_own_alloc (Excl ())); ss. iIntros "[%γ TKN]".
    iMod (inv_alloc (SpinLockAS.lock_inv blk 0 P γ) u_a _ _ N_SpinLockA with "[P PT TKN]") as "#I"; eauto.
    { rewrite /lock_inv /=; SL_red; iRight; iFrame. }
    forces_l. iFrame. iSplit; eauto.
    { iSplit; eauto. rewrite /is_lock. iExists _, _; iSplit; eauto. }
    steps_l. step. eauto.
  (*FAST*)Qed.

  Lemma acquire_simF : HSim.sim_fun open MA MI IstFull SpinLockHdr.acquire.
  Proof.
    init_simF u_a 0.
    (* process src precondition *)
    steps_l. iDestruct "ASM" as "[[% [TID #LOCK]] %]". hss.
    iDestruct "LOCK" as (? ?) "[% LOCK]". steps_r.
    (* start coinduction for lock acquire/failure *)
    iApply wsim_reset.
    iStopProof. revert nths. combine_quant NODS. combine_quant NODD.
    combine_quant st_src. combine_quant st_tgt.
    eapply wsim_coind. ii.
    destruct a as [st_tgt [st_src [NODD [NODS nths]]]]. ss.
    iIntros "[#LOCK [IST TID]] _ #CIH".
    unfold_iter_l. steps_l.
    unfold_iter_r. steps_r.
    (* tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_tgt st_src NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl". SL_red.
    iDestruct "I" as "[FAIL|SUCC]".
    { (* fail case *)
      (* tgt inline - mem cas *)
      inline_r. forces_r. 
      instantiate (1:= existT _ _). hss. instantiate (2:= 1). ss.
      instantiate (1:= (_, _, _, _, _)). hss. 
      iSplitL "FAIL". iFrame. et.
      steps_r.
      iDestruct "GRT" as "[[POINTS_TO %] %]".
      hss. steps_r.
      iMod ("Hcl" with "[POINTS_TO]") as "_". iFrame.
      (* tgt yields *)
      sch_yield_r. iFrame.
      clear nths st_t st_s NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
      sch_yield_r. iFrame.
      clear nths st_t st_s NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
      (* src yield - choose false for looping again *)
      sch_yield_l. force_l false. steps_l. step_r.
      by_coind "CIH".
      iFrame. done.
    }
    { (* success case *)
      (* tgt inline - mem cas *)
      iDestruct "SUCC" as "[POINTS_TO [Q TKN]]".
      inline_r. forces_r.
      instantiate (1:= existT _ _). ss. instantiate (2:= 0). ss.  
      instantiate (1:= (_, _, _, _)). hss. iSplitL "POINTS_TO"; iFrame; et. 
      steps_r.
      iDestruct "GRT" as "[[POINTS_TO ->] ->]". hss.
      steps_r.
      iMod ("Hcl" with "[POINTS_TO]") as "_". iFrame.
      (* tgt yields *)
      sch_yield_r. iFrame.
      clear nths st_t st_s NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
      sch_yield_r. iFrame.
      clear nths st_t st_s NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
      sch_yield_r. iFrame.
      clear nths st_t st_s NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
      (* src yield *)
      sch_yield_l. force_l true. steps_l. forces_l. iSplitL "Q TKN TID"; SL_red; et. iFrame. et.
      (* both terminate *)
      step; eauto.
    }
    Unshelve. all: eauto.
  (*FAST*)Qed.

  Lemma release_simF : HSim.sim_fun open MA MI IstFull SpinLockHdr.release.
    init_simF u_a 0.
    (* process src precondition *)
    steps_l.
    iDestruct "ASM" as "[(% & TID & #LOCK & TKN & Q) %]".
    iDestruct "LOCK" as (? ?) "[% LOCK]".
    hss.
    steps_r.
    (* tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_tgt st_src NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
    (* open invariant *)
    iInv "LOCK" as "I" "Hcl". SL_red.
    iDestruct "I" as "[LOCKED|UNLOCKED]".
    { (* locked case *)
      inline_r. steps_r. forces_r. instantiate (1:= (_, _)).
      ss. instantiate (2:=(_, _)). ss.
      iSplitL "LOCKED"; iFrame; et.
      steps_r. iDestruct "GRT" as "[[POINTS_TO %] %]". hss.
      steps_r.
      iMod ("Hcl" with "[POINTS_TO Q TKN]") as "_". iRight. iFrame.
      (* tgt yield *)
      sch_yield_r. iFrame.
      clear nths st_t st_s NODD NODS; iIntros (nths st_s st_t NODD NODS) "IST TID".
      (* src yield *)
      sch_yield_l. steps_l. forces_l. iFrame. iSplit; et. step. iFrame; et.
    }
    { (* unlocked case - ex falso quodlibet *)
      iDestruct "UNLOCKED" as "[POINTS_TO [Q' TKN']]".
      iCombine "TKN TKN'" gives %Hv. done.
    }
  (*FAST*)Qed.

  (* Construct HSim.t for summing up each simulation proofs *)
  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; iSplit; eauto. }
    { apply newlock_simF. }
    { apply acquire_simF. }
    { apply release_simF. }
  Qed.
End SpinLockIA.
Section SpinLockIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !SpinLockAGΓ Γ}.
  (* ctxr works as a unit in compositions of module simulations *)
  Lemma ctxr (u : univ_id) (spc_s spc_user_s spc_mem : string → option fspec)
      (SchInSpc : spc_incl (SchAS.spc u spc_user_s) spc_s)
      (MemInSpc : spc_incl MemA.spc spc_s) :
    ctx_refines
      (SpinLockA.t u spc_s ★ MemA.t u spc_mem, emp%I)
      (SpinLockI.t         ★ MemA.t u spc_mem, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End SpinLockIA. End SpinLockIA.