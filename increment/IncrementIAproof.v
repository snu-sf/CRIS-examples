Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA.
From CRIS.increment Require Import Header IncrementI IncrementA.

Module IncrementIA. Section IncrementIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition IstFull := (IstProd (IstSB IncrementA.t.(Mod.scopes) Ist) IstEq).
  Local Definition MA := (IncrementA.t ★ MemA.t).
  Local Definition MI := (IncrementI.t ★ MemA.t).

  Lemma increment_simF : ISim.sim_fun open MA MI True%I IstFull (Some IncrementHdr.increment).
  Proof.
    init_simF.
    steps_l. destruct _q; ss. destruct _q; ss. destruct v; ss. inv G0. hss.
    destruct _q0 as [blk ofs].

    steps_r. sch_yield_rr; iFrame; iSplit; eauto. sch_intros. iClear "TID".
    steps_r. sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID".
    sch_yield_l.
    norm_l. norm_r.

    iApply wsim_reset.
    iStopProof. revert nths. clear NODS NODT. combine_quant st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' [st_t [st_s nths]]) "IST %GG' #CIH /=".

    unfold_iter_l. unfold_iter_r.
    steps_l. steps_r.
    sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID".
    Unshelve. all: try exact 0.

    sch_yield_l. steps_l. rename _q into v.

    steps_r. inline_r. force_r (blk, ofs, 1%Qp, Vint v). steps_r.
    forces_r. iFrame "ASM". iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss_r. steps_r.

    force_l false. steps_l. force_l; iFrame "PT". steps_l. sch_yield_l. steps_l.
    unfold_iter_l. steps_l.

    sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID". steps_r.
    sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID". steps_r.

    sch_yield_l. steps_l. rename _q into v'.
    inline_r. force_r (_, _, _, _, _, _, _, _, _, _). forces_r. iFrame "ASM".
    iSplitL ""; eauto.
    { iSplit; eauto. iSplit; [iPureIntro; split; [refl|ss]|ss]. des_ifs. }
    Unshelve. all: try exact 0; try exact 1%Qp; try exact (Vint 0).

    steps_r. iDestruct "GRT" as "[[-> [GRT _]] ->]". hss_r. steps_r.
    destruct (dec v' v) as [?|Heq]; [subst; ss|ss].
    { force_l true. steps_l. force_l; iFrame "GRT"; steps_l.
      sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID". steps_r.
      sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID". steps_r.
      case_decide; [|ss].
      steps_r.
      sch_yield_l. steps_l. step. iSplit; done.
    }
    { force_l false.
      forces_l. iFrame "GRT". steps_l.
      sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID". steps_r.
      sch_yield_rr; iFrame "IST". iSplit; eauto. sch_intros. iClear "TID". steps_r.
      case_decide; first clarify.
      steps_r.
      sch_yield_l. steps_l.
      iApply wsim_progress. iApply wsim_base.
      iIntros "?". iApply ("CIH" $! (st_tgt, (st_src, nths))). iFrame.
    }
    Unshelve. all: eauto.
  (*SLOW*)Admitted.
End IncrementIA. End IncrementIA.
