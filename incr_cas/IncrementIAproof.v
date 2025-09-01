Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA.
From CRIS.incr_cas Require Import Header IncrementI IncrementA.

Module IncrementIA. Section IncrementIA.
  Context `{CrisG: !crisG Γ Σ α β τ _S _I}.
  Context `{MemG: !memG}.
  Context `{SchG: !schG}.

  Local Definition IstFull := (IstProd (IstSB IncrementA.t.(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (IncrementA.t ★ MemA.t).
  Local Definition MI := (IncrementI.t ★ MemA.t).

  Lemma increment_simF : ISim.sim_fun open MA MI True%I IstFull (Some IncrementHdr.increment).
  Proof using MemG SchG.
    init_simF.
    steps_l. destruct _q; ss. destruct _q; ss. destruct v; ss. inv G0. hss.
    destruct _q0 as [blk ofs].

    steps_r.
    sch_yield_rr.
    steps_r. sch_yield_rr.
    sch_yield_l.
    norm_l. norm_r.

    iApply wsim_reset.
    iStopProof. revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_t st_s]) "%GG' /=".
    destruct_quant CIH.

    unfold_iterC_l. unfold_iterC_r.
    steps_l. steps_r.
    sch_yield_rr.
    Unshelve. all: try exact 0.

    sch_yield_l. steps_l. rename _q into v.

    steps_r. inline_r. force_r (blk, ofs, 1%Qp, Vint v). steps_r.
    forces_r. iFrame "ASM". iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss_r. steps_r.

    force_l false. steps_l. force_l; iFrame "PT". steps_l. sch_yield_l. steps_l.
    unfold_iterC_l. steps_l.

    sch_yield_rr. steps_r.
    sch_yield_rr. steps_r.

    sch_yield_l. steps_l. rename _q into v'.
    inline_r. force_r (_, _, _, _, _, _, _, _, _, _). forces_r. iFrame "ASM".
    iSplitL ""; eauto.
    { iSplit; eauto. iSplit; [iPureIntro; split; [refl|ss]|ss]. des_ifs. }
    Unshelve. all: try exact 0; try exact 1%Qp; try exact (Vint 0).

    steps_r. iDestruct "GRT" as "[[-> [GRT _]] ->]". hss_r. steps_r.
    destruct (dec v' v) as [?|Heq]; [subst; ss|ss].
    { force_l true. steps_l. force_l; iFrame "GRT"; steps_l.
      sch_yield_rr. steps_r.
      sch_yield_rr; steps_r.
      case_decide; [|ss].
      steps_r.
      sch_yield_l. steps_l. step. iSplit; done.
    }
    { force_l false.
      forces_l. iFrame "GRT". steps_l.
      sch_yield_rr; steps_r.
      sch_yield_rr; steps_r.
      case_decide; first clarify.
      steps_r.
      sch_yield_l. steps_l.
      iApply wsim_progress. iApply wsim_base.
      iIntros "?". iApply (CIH). iFrame.
    }
    Unshelve. all: eauto.
  (*SLOW*)Qed.
End IncrementIA. End IncrementIA.
