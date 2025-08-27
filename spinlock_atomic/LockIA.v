Require Import CRIS.
Require Import ImpPrelude MemA.
Require Import SchHeader SchA SchTactics.
From CRIS.spinlock_atomic Require Import Header LockI LockA.

Module LockIA. Section LockIA.
  Import LockAS.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG, !spinlockG}.

  Context (E : coPset).
  Context (LockInE: ↑N_SpinLockA ⊆ E).  
  
  Definition init_cond : iProp Σ := emp%I.

  Local Definition MemP := MemP.t.
  Local Definition SpinLockA := SpinLockA.t.
  Local Definition SpinLockI := SpinLockI.t.
  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SpinLockA E)) IstTrue) IstEq).
  Local Notation MA := (SpinLockA E ★ MemP).
  Local Notation MI := (SpinLockI ★ MemP).

  Lemma newlock_simF :
    ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.newlock).
  Proof.
    init_simF.
    steps_l; unfold_real_lat_l.

    destruct (arg↓) as [v|] eqn: EQ; cycle 1.
    { sch_yield_l. steps_l. force_l (tt↑). steps_l.
      ru_l False%I. iSplitL; cycle 1.
      { iIntros "F". iExFalso. et. }
      iIntros ([]) "[_ [[% _] _]]"; subst; hss.
    }
    steps_r. sch_yield_rr.

    (* tgt inline - mem alloc *)
    steps_r. inline_r. steps_r.
    unfold_real_lat_r. force_r 1.
    iSplit; et. iIntros "[%blk [-> [↦ _]]]".
    steps_r; hss_r; steps_r.
    sch_yield_rr.

    (* tgt inline - mem store *)
    steps_r. inline_r. steps_r.
    unfold_real_lat_r. force_r (blk, 0%Z, _, _); s.
    iFrame "↦". iSplit; try done. iIntros "[↦ ->]".
    steps_r; hss_r; steps_r.

    (* src/tgt yield *)
    sch_yield_rr. sch_yield_l; steps_l.

    (* lock token allocation *)
    iMod (own_alloc (Excl ())) as "[%γ TKN]"; [done|].
    force_l ((Vptr (blk, 0%Z))↑). steps_l.
    ru_l emp%I.
    iSplitR "IST"; cycle 1.
    { iIntros "_". steps_l. sch_yield_l. step. iSplit; done. }
    iIntros ([n P]) "[W [[_ P] _]]"; s.
    iSplitR; [eauto|].
    unfold_pre_post. iRevert "W".
    iApply (winv_fupd (S n)).
    iMod (inv_alloc (LockAS.lock_inv (blk, 0%Z) P γ) _ _ _ N_SpinLockA
      with "[↦ P TKN]") as "#I"; ss.
    { rewrite /lock_inv; SL_red; iRight; iFrame. }
    iModIntro; iFrame. iSplit; eauto. iExists _, _; iSplit; eauto.
    rewrite /is_lock; iExists _; iFrame "I"; done.
    Unshelve. all: exact 0.
  (*SLOW*)Qed.

  Lemma acquire_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.acquire).
  Proof.
    init_simF.
    steps_l; unfold_real_lat_l.

    (* ill-formed argument *)
    destruct (arg↓) as [l|] eqn : Heqarg; cycle 1.
    { sch_yield_l. steps_l. force_l false. force_l (tt↑). steps_l.
      ru_l False%I. iSplitL; cycle 1.
      { iIntros "F". iExFalso. et. }
      iIntros ([[] []]) "[_ [[% _] _]]"; subst; hss.
    }
    destruct (or_else (pargs [Tptr] l) (0, 0%Z)) as [blk ofs] eqn: EQ.
    hss. steps_r.

    (* start coinduction for lock acquire/failure *)
    iApply wsim_reset. iStopProof.
    revert st_tgt. combine_quant st_src.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_src st_tgt]) "IST /=".
    destruct_quant CIH.

    unfold_iter_r. steps_r. sch_yield_rr. sch_yield_l; steps_l.
    steps_r. inline_r. steps_r.
    unfold_real_lat_r.
    ru_r. iIntros (pr) "UPD". rename _q into ret.

    destruct (classic (ret = (Vint 0)↑)).
    { force_l false. steps_l. force_l (Vundef↑). steps_l.
      ru_l (Own pr)%I.
      iSplitL "UPD".
      { iIntros ([[γ vl] [n P]]) "/= [W [[% [%bofs #[% I]]] %]]"; destruct bofs as [blk' ofs'].
        iRevert "W". iInv "I" as "INV" "ACC". hss.
        iEval (SL_red) in "INV". iDestruct "INV" as "[PT | [PT [R TKN]]]".
        { iPoseProof ("UPD" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [_ [% _]]".
          - iFrame "PT". iSplit; eauto.
          - hss.
        }
        iPoseProof ("UPD" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [$ [% [↦ _]]] /=".
        { s. iFrame "PT". iSplit; eauto. }
        Unshelve. all: try exact 1%Qp; try exact (Vint 0); eauto.
        hss. iMod ("ACC" with "[↦]") as "_".
        { SL_red; iFrame "↦". }
        iIntros "$ !>"; iSplit; et.
        unfold_pre_post. SL_red. iFrame. et.
      }
      iIntros "PR".
      steps_l. force_r; iFrame. steps_r. hss. steps_r.
      do 3 sch_yield_rr.
      sch_yield_l.
      step. et.
    }
    { force_l true. steps_l.
      ru_l (⌜ret = (Vint 1)↑⌝ ∗ Own pr)%I.
      iSplitL "UPD".
      { iIntros ([[γ vl] [n P]]) "/= [W [[% [%bofs #[% I]]] %]]"; destruct bofs as [blk' ofs'].
        iRevert "W". iInv "I" as "INV" "ACC". hss.
        iEval (SL_red) in "INV". iDestruct "INV" as "[PT| [PT [R TKN]]]"; cycle 1.
        { iPoseProof ("UPD" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [_ [% _]]".
          - s. iFrame "PT". iSplit; eauto.
          - hss.
        }
        iPoseProof ("UPD" $! (_, _, _, _, _, _, _, _, _, _) with "[PT]") as "> [$ [% [↦ _]]] /=".
        { s. iFrame "PT". iSplit; eauto. }
        Unshelve. all: try exact 1%Qp; try exact (Vint 0); eauto.
        hss. iMod ("ACC" with "[↦]") as "_".
        { SL_red; iFrame "↦". }
        iIntros "$ !>". repeat (iSplit; et).
        iExists _; iFrame "I"; done.
      }
      iIntros "[-> PR]".
      steps_l. unfold_real_lat_l.
      force_r; iFrame. steps_r. hss. steps_r.
      do 2 sch_yield_rr. steps_r.
      by_coind CIH. iFrame.
    }
  Unshelve. all: try exact 1%Qp; try exact (Vint 0); eauto.
  (*SLOW*)Qed.

  Lemma release_simF : ISim.sim_fun open MA MI init_cond IstFull (Some SpinLockHdr.release).
  Proof.
    init_simF.
    steps_l; unfold_real_lat_l.

    (* ill-formed argument *)
    destruct (arg↓) as [l|] eqn : Heqarg; cycle 1.
    { sch_yield_l. steps_l. force_l (tt↑). steps_l.
      ru_l False%I. iSplitL; cycle 1.
      { iIntros "F". iExFalso. et. }
      iIntros ([[] []]) "[_ [[% _] _]]"; subst; hss.
    }
    destruct (or_else (pargs [Tptr] l) (0, 0%Z)) as [blk ofs] eqn: EQ.

    steps_r. sch_yield_rr.
    steps_r. inline_r. steps_r.
    unfold_real_lat_r.
    ru_r. iIntros (pr) "UPD". rename _q into ret.
    sch_yield_l; steps_l. force_l (Vundef↑). steps_l.
    ru_l (⌜ret = (Vint 0)↑⌝ ∗ Own pr)%I.
    iSplitL "UPD".
    { iIntros ([[γ v] [n R]]) "[W [[% [[% [-> #I]] [TKN R]]] _]] /=". hss.
      iRevert "W". iInv "I" as "INV" "ACC".
      iEval (SL_red) in "INV"; iDestruct "INV" as "[PT | [PT [R' TKN']]]"; cycle 1.
      { SL_red; iCombine "TKN" "TKN'" gives %WF; inv WF. }
      iPoseProof ("UPD" $! (_, _, _, _) with "[PT]") as "> [$ [↦ %]]".
      { ss; iFrame "PT"; done. }
      iMod ("ACC" with "[TKN R ↦]") as "_".
      { SL_red. iRight; iFrame. }
      iIntros "$ !>"; eauto.
    }

    iIntros "[-> ?]"; force_r; iFrame.
    steps_l. steps_r; hss_r. steps_r.
    sch_yield_rr.
    sch_yield_l; steps_l; step. et.
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
      (SpinLockA.t E ★ MemP.t, emp%I)
      (SpinLockI.t ★ MemP.t, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End LockIA. End LockIA.
