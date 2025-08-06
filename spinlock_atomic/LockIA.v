(* Require Import CRIS.
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
    rewrite /fspec_proph; unfold_iter_l; steps_l.
    rename _q into varg.

    (* tgt yield *)
    sch_yield_rr; iFrame; iSplit; [done|]; sch_intros; iClear "TID".

    (* tgt inline - mem alloc *)
    steps_r. inline_r. steps_r.
    rewrite /fspec_proph; unfold_iter_r; steps_r.
    iApply wsim_assume_proph_tgt; iExists 1; iSplit; [done|].
    iIntros (?) "Q !>". steps_r.
    iApply wsim_guarantee_proph_tgt; iIntros (ret) "Post !>".
    iMod ("Post" with "Q") as "[%blk [% [↦ _]]]".
    hss. steps_r. hss_r. steps_r.

    (* tgt yield *)
    sch_yield_rr; iFrame; iSplit; [done|]; sch_intros; iClear "TID".

    (* tgt inline - mem store *)
    steps_r. inline_r.
    steps_r. rewrite /fspec_proph; unfold_iter_r; steps_r.
    iApply wsim_assume_proph_tgt; iExists (blk, 0%Z, _, _); s; iFrame "↦".
    iSplit; [done|]; clear Q; iIntros (Q) "Q !>". steps_r.
    iApply wsim_guarantee_proph_tgt; iIntros (ret) "Post !>".
    steps_r; hss_r; steps_r.
    iMod ("Post" with "Q") as "[↦ %]".

    (* src/tgt yield *)
    sch_yield_rr; iFrame; iSplit; [done|]; sch_intros; iClear "TID"; steps_r.
    sch_yield_l; steps_l.

    (* lock token allocation *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].

    iApply wsim_assume_proph_src.
    set (post := λ _ _, _).
    iExists emp%I, (λ x, post x (Vptr (blk, 0%Z))).
    iSplit; [iApply precise_emp|].
    iSplitL "↦ TKN"; cycle 1.
    { iIntros "_ !>". steps_l.
      iApply wsim_guarantee_proph_src; iExists (Vptr (blk, 0%Z)).
      iSplitR; [iIntros "% $ //"|].
      steps_l. step. iSplit; done.
    }
    { iIntros ([n P]) "[W [P Q]]"; s.
      iSplitR; eauto.
      subst post; ss. unfold_pre_post.
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
    steps_l. steps_r. hss.
    rewrite /fspec_proph_option.

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
    rewrite /fspec_proph; unfold_iter_r; steps_r.
    rename _q0 into v.

    iApply wsim_assume_proph_both.
    destruct (or_else (pargs [Tptr] _q) (0, 0%Z)) as [blk ofs] eqn: EQ.
    iIntros (pr_t Q_t) "Post"; iExists (Own pr_t).
    set (post := λ _ _, _).
    set (pre := λ (_ : positive * _ * _), (_ : iProp Σ)).
    iExists (λ x,
      ((blk, ofs) ↦ (Vint 1) ==∗ post x (Some Vundef)) ∧ ((blk, ofs) ↦ (Vint 0) ==∗ pre x))%I.
    iSplitR; [iApply precise_Own|].
    iSplitL "Post".
    { iClear "CIH".
      iIntros ([[γ lv] [n P]]); unfold_pre_post.
      iIntros "[W [[% #[%bofs [-> I]]] %]]"; hss.
      iRevert "W".
      iInv "I" as "INV" "ACC".
      iEval (SL_red) in "INV"; iDestruct "INV" as "[PT | [PT [R TKN]]]".
      { iPoseProof ("Post" $! (blk, ofs, Vint 1, 1%Qp, Vundef, Vint 0, 1%Qp, Vundef, _, _) with "[PT]") as "> [PR Q]".
        { ss. iFrame "PT". iSplit; eauto. }
        iIntros "W !>"; iFrame "PR"; iSplit.
        { iIntros "↦".
        }
      }
      { iPoseProof ("Post" $! (blk, ofs, Vint 0, 1%Qp, Vundef, _, 1%Qp, Vundef, _, _) with "[PT]") as "> [PR Q]".
        { ss. iFrame "PT". iSplit; eauto. }
        iIntros "W !>"; iFrame "PR Q ACC".
      }
    }

    iIntros "$ !>".
    steps_l. steps_r.
    iApply wsim_guarantee_proph_tgt.
    iIntros (ret) "Post !>".

    destruct (dec ret (Vint 0)).
    { iClear "CIH".
      iApply wsim_guarantee_proph_src.
      iExists (Some Vundef); iSplitL "Post".
      { iIntros ([[γ vl] [n P]]) "[ACC [% Q]]".
        unfold_pre_post.
      force_l Vundef; force_l P; force_l.
      iSplitL "GRT".
      { iIntros ([[γ ?] [n R]]) "[W [[% #I] %]] /="; hss.
        iRevert "W".
        iDestruct "I" as "[%bofs [-> #INV]]"; destruct bofs as [blk ofs].
        iInv "INV" as "I" "ACC".
        iEval (SL_red) in "I"; iDestruct "I" as "[PT | [PT [R TKN]]]".
        { iPoseProof ("GRT" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [$ [% COMM]]".
          { ss; iFrame; iSplit; eauto. }
          hss.
        }
        { iPoseProof ("GRT" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [$ [_ [COMM _]]]".
          { ss; iFrame; iSplit; eauto. }
          iMod ("ACC" with "[COMM]") as "_".
          { SL_red; iFrame. }
          SL_red; iIntros "$"; iFrame; done.
        }
      }
      Unshelve. all: try exact 1%Qp; try exact Vundef.
      steps_l. force_l; iFrame. steps_l.
      iApply wsim_assume_res_both.
      steps_l; steps_r.
      hss_r; steps_r.
      sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID". steps_r.
      sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID". steps_r.
      sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID". steps_r.
      sch_yield_l; steps_l. force_l; step.
      iFrame. done.
      Unshelve. all: eauto.
    }
    { force_l (Vint 1). force_l (P ∗ ⌜v = Vint 1⌝)%I. force_l.
      iSplitL "GRT".
      { iIntros ([[γ ?] [? R]]) "[W [[% #I] %]] /="; hss.
        iRevert "W".
        iDestruct "I" as "[%bofs [-> #INV]]"; destruct bofs as [blk ofs].
        iInv "INV" as "I" "ACC".
        iEval (SL_red) in "I"; iDestruct "I" as "[PT | [PT [R TKN]]]"; cycle 1.
        { iPoseProof ("GRT" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [$ [% COMM]]".
          { ss; iFrame; iSplit; eauto. }
          hss.
        }
        { iPoseProof ("GRT" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [$ [% [COMM ?]]]".
          { ss; iFrame; iSplit; eauto. }
          iMod ("ACC" with "[COMM]") as "_ /=".
          { SL_red; iFrame. }
          SL_red; iIntros "$ !>"; iFrame "INV". hss.
        }
      }
      steps_l. iPoseProof "GRT'" as "#?". force_l. iSplit.
      { iApply precise_sep; iSplit; eauto; iApply precise_pure. }
      force_l.
      { iApply precise_sep; iSplit; eauto; iApply precise_pure. }
      iDestruct "ASM" as "[P ->]".
      force_r. iFrame "P".
      steps_l; steps_r.
      hss_r; steps_r.
      sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID". steps_r.
      sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID". steps_r.
      sch_yield_l; steps_l.

      by_coind "CIH".
      iFrame.
    }
    Unshelve. all: try exact 1%Qp; try exact Vundef; eauto.
  (*SLOW*)Admitted.

  Lemma release_simF :
    ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.release).
  Proof using.
    init_simF.
    (* process src precondition *)
    steps_l. hss. steps_r.
    rewrite /fspec_proph_abort; unfold_iter_l; steps_l.
    sch_yield_rr; iFrame; iSplit; et; sch_intros; iClear "TID". steps_r.
    inline_r. steps_r.
    sch_yield_l. steps_l.
    rewrite /AssumeProph; unseal "CRIS-PROPH"; steps_r.
    rename _q0 into P, _q1 into Q.
    force_l Vundef; force_l P; force_l.
    iSplitL "GRT".
    { iIntros ([[γ v] [n R]]) "[W [[% [[% [-> #INV]] [TKN R]]] ?]] /=". hss.
      destruct bofs as [blk ofs].
      iRevert "W".
      iInv "INV" as "I" "ACC".
      iEval (SL_red) in "I"; iDestruct "I" as "[PT | [PT [R' TKN']]]"; cycle 1.
      { SL_red; iCombine "TKN TKN'" gives %WF; inv WF. }
      iPoseProof ("GRT" $! (_, _, _, _) with "[PT]") as "> [$ COMM]".
      { iFrame "PT"; done. }
      iIntros "W !> %ret [-> [% Q]]".
      iMod ("COMM" with "Q") as "[COMM ->] /=".
      iRevert "W"; iMod ("ACC" with "[COMM R TKN]") as "_".
      { SL_red; iRight; iFrame. }
      by iIntros "$ !>".
    }
    step_l. iApply wsim_assume_res_both.
    steps_l. force_l (Vundef↑). steps_l.
    steps_r.
    force_l; iFrame "GRT"; iSplit; eauto. steps_l.
    asmproph_standard.
    iExists P, Q.

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
      steps_r. inline_r. steps_r. force_r (_,_,_,_). iSplitL "LOCKED"; iFrame; et.
      iIntros (?) "Q'". steps_r. iMod ("Q'" with "GRT") as "[POINTS_TO %]".
      hss. steps_r.
      iMod ("Hcl" with "[POINTS_TO Q TKN]") as "_". iRight. iFrame.
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
      (SpinLockA.t E q sp ★ MemP.t, emp%I)
      (SpinLockI.t        ★ MemP.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End LockIA. End LockIA. *)
