Require Import CRIS.
Require Import ImpPrelude MemA.
Require Import SchHeader SchA SchTactics.
From CRIS.spinlock_atomic Require Import Header LockI LockA.

Module LockIA. Section LockIA.
  Import LockAS.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG, !spinlockG}.

  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemP := MemP.t.
  Local Definition SpinLockA := SpinLockA.t.
  Local Definition SpinLockI := SpinLockI.t.
  Local Definition IstFull := (IstProd (IstSB (Mod.scopes SpinLockA) IstTrue) IstEq).
  Local Notation MA := (SpinLockA ★ MemP).
  Local Notation MI := (SpinLockI ★ MemP).

  Lemma newlock_simF :
    ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.newlock).
  Proof.
    init_simF.

    (* preprocess initial conditions *)
    steps_l. hss. steps_r.
    rewrite /fspec_proph_update; unfold_iter_l; steps_l.
    destruct (arg↓) as [v|]; cycle 1.
    { sch_yield_l. steps_l.
      des_ifs; [replace_l; [eapply vis_trigger|]|replace_l; [eapply vis_trigger|]]; step_l; ss.
    }

    (* tgt yield *)
    steps_r.
    sch_yield_rr; iFrame; iSplit; [done|]; sch_intros; iClear "TID".

    (* tgt inline - mem alloc *)
    steps_r. inline_r. steps_r.
    rewrite /fspec_proph_update; unfold_iter_r; steps_r.
    hss_r. steps_r.
    iApply wsim_update_proph_tgt; iExists 1; iSplit; [done|].
    iIntros (?) "[%blk [% [↦ _]]]"; hss.
    steps_r. hss_r. steps_r.

    (* tgt yield *)
    sch_yield_rr; iFrame; iSplit; [done|]; sch_intros; iClear "TID".

    (* tgt inline - mem store *)
    steps_r. inline_r.
    steps_r. rewrite /fspec_proph_update; unfold_iter_r; steps_r.
    hss_r; steps_r.
    iApply wsim_update_proph_tgt; iExists (blk, 0%Z, _, _); s; iFrame "↦".
    iSplit; [done|]; iIntros (ret) "[↦ %]"; steps_r.
    hss_r; steps_r.

    (* src/tgt yield *)
    sch_yield_rr; iFrame; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
    sch_yield_l; steps_l.

    (* lock token allocation *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].

    iApply wsim_update_proph_src.
    iExists emp%I, (Vptr (blk, 0%Z)).
    iSplit; [iApply precise_emp|].
    iSplitL "↦ TKN"; cycle 1.
    { iIntros "_ !>". steps_l. step. iSplit; done. }
    { iIntros ([n P]) "[W [P _]]"; s.
      iSplitR; [eauto|].
      unfold_pre_post.
      iRevert "W".
      iApply (winv_fupd (S n)).
      iMod (inv_alloc (LockAS.lock_inv (blk, 0%Z) P γ) _ _ _ N_SpinLockA
        with "[↦ P TKN]") as "#I"; ss.
      { rewrite /lock_inv; SL_red; iRight; iFrame. }
      iModIntro; iFrame. iSplit; eauto. iExists _, _; iSplit; eauto.
      rewrite /is_lock; iExists _; iFrame "I"; done.
      Unshelve. all: eauto.
    }
  (*SLOW*)Admitted.

  Lemma acquire_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.acquire).
  Proof.
    init_simF.

    (* process src precondition *)
    steps_l. steps_r.
    rewrite /fspec_proph_update_option.

    (* ill-formed argument *)
    destruct (arg↓) as [l|] eqn : Heqarg; cycle 1.
    { unfold_iter_l; steps_l.
      sch_yield_l; step_l.
      des_ifs; rewrite vis_trigger; steps_l; ss.
    }
    destruct (or_else (pargs [Tptr] l) (0, 0%Z)) as [blk ofs] eqn: EQ.

    steps_r.
    (* start coinduction for lock acquire/failure *)
    iApply wsim_reset.
    iStopProof. revert nths. clear NODS NODT.
    combine_quant st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' [st_tgt [st_src nths]]) "IST _ #CIH /=".

    unfold_iter_r; steps_r.
    unfold_iter_l; steps_l.
    sch_yield_rr; iFrame "IST"; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
    Unshelve. all: eauto.
    sch_yield_l; steps_l.
    steps_r; inline_r; steps_r.
    rewrite /fspec_proph_update; unfold_iter_r; steps_r.
    hss_r. steps_r.

    iApply wsim_update_proph_both.
    iIntros (ret_t P_t) "#Pre Hsplit".
    iExists (P_t ∗ ⌜ret_t = Vint 0 ∨ ret_t = Vint 1⌝)%I,
      (if dec ret_t (Vint 0) then Some (Vundef) else None).
    iSplit; [iApply precise_sep; iSplit; [done|iApply precise_pure]|].
    iSplitL "Hsplit".
    { iIntros ([[γ vl] [n P]]) "/= [W [[% [%bofs #[% I]]] %]]"; destruct bofs as [blk' ofs'].
      hss. iRevert "W".
      iInv "I" as "INV" "ACC".
      iEval (SL_red) in "INV"; iDestruct "INV" as "[PT | [PT [R TKN]]]".
      { iPoseProof ("Hsplit" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> Hsplit".
        { s. iFrame "PT". iSplit; eauto. }
        Unshelve. all: try exact 1%Qp; try exact Vundef.
        iDestruct "Hsplit" as "[$ [% [↦ _]]] /=". hss.
        iMod ("ACC" with "[↦]") as "_".
        { SL_red; iFrame "↦". }
        iIntros "$ !>"; iSplit; [eauto|iSplit; [iSplit; [done|]|done]].
        iExists _; iFrame "I"; done.
      }
      { iPoseProof ("Hsplit" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> Hsplit".
        { s. iFrame "PT". iSplit; eauto. }
        Unshelve. all: try exact 1%Qp; try exact Vundef.
        iDestruct "Hsplit" as "[$ [% [↦ _]]] /=". hss.
        iMod ("ACC" with "[↦]") as "_".
        { SL_red; iFrame "↦". }
        iIntros "$ !>"; iSplit; [eauto|].
        unfold_pre_post. iSplit; eauto. SL_red; iFrame. done.
      }
    }
    iIntros "[$ [->|->]] !>".
    { steps_r. hss_r. steps_r.
      steps_l.
      sch_yield_rr; iFrame "IST"; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
      sch_yield_rr; iFrame "IST"; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
      sch_yield_rr; iFrame "IST"; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
      sch_yield_l; steps_l; step.
      iFrame; done.
    }
    { steps_r. hss_r; steps_r.
      steps_l.
      unfold_iter_l; steps_l.
      sch_yield_rr; iFrame "IST"; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
      sch_yield_rr; iFrame "IST"; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
      sch_yield_l; step_l.
      iApply wsim_update_proph_src.
      iExists emp%I, None.
      iSplit; [iApply precise_emp|].
      iSplitR; [iIntros (?) "$ !> //"|].
      iIntros "_ !>"; steps_l.
      by_coind "CIH".
      iFrame.
    }
    Unshelve. all: eauto.
  (*SLOW*)Admitted.

  Lemma release_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.release).
  Proof.
    init_simF.
    (* process src precondition *)
    steps_l. rewrite /fspec_proph_update; unfold_iter_l; steps_l.
    steps_r.

    (* ill-formed argument *)
    destruct (arg↓) as [l|] eqn : Heqarg; cycle 1.
    { sch_yield_l; step_l.
      des_ifs; rewrite vis_trigger; steps_l; ss.
    }
    destruct (or_else (pargs [Tptr] l) (0, 0%Z)) as [blk ofs] eqn: EQ.
    steps_r.
    sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID".
    steps_r. inline_r. steps_r. rewrite /fspec_proph_update; unseal CRIS_PROPH.
    unfold_iter_r; steps_r.
    hss_r; steps_r.
    sch_yield_l; steps_l.

    iApply wsim_update_proph_both.
    iIntros (ret_t P_t) "#Precise Hsplit"; iExists (P_t), Vundef.
    iSplit; [done|].
    iSplitL "Hsplit".
    { iIntros ([[γ v] [n R]]) "[W [[% [[% [-> #I]] [TKN R]]] _]] /=". hss.
      hss. iRevert "W".
      iInv "I" as "INV" "ACC".
      iEval (SL_red) in "INV"; iDestruct "INV" as "[PT | [PT [R' TKN']]]"; cycle 1.
      { SL_red; iCombine "TKN" "TKN'" gives %WF; inv WF. }
      iPoseProof ("Hsplit" $! (_, _, _, _) with "[PT]") as "> [$ [↦ %]]".
      { ss; iFrame "PT"; done. }
      iMod ("ACC" with "[TKN R ↦]") as "_".
      { SL_red. iRight; iFrame. }
      iIntros "$ !>"; eauto.
    }

    iIntros "$ !>".
    steps_l.
    steps_r; hss_r.
    sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID". steps_r.
    sch_yield_l; steps_l; step.

    iFrame; done.
    Unshelve. all: eauto.
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
      (SpinLockA.t ★ MemP.t, emp%I)
      (SpinLockI.t ★ MemP.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End LockIA. End LockIA.
