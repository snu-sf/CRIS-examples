Require Import CRIS.
From CRIS.incr_faa Require Import Header FaaI FaaA.
Require Import ImpPrelude MemHeader MemA SchA SchTactics SchHeader.

Module FaaIA. Section FaaIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG}.

  Local Definition IstFull := (IstProd (IstSB FaaA.t.(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (FaaA.t ★ MemP.t).
  Local Definition MI := (FaaI.t ★ MemP.t).

  Lemma faa2_simF : ISim.sim_fun open MA MI True%I IstFull (Some FaaHdr.faa2).
  Proof.
    init_simF.

    steps_l.
    destruct _q0 as [blk ofs]. destruct _q as [ | v [|? ?]]; ss; destruct v; ss.
    hss. inv G0.

    steps_l. steps_r.

    sch_yield_rr.
    sch_yield_l; steps_l. rename _q into v.

    rewrite /MemHdr.faa; steps_r; inline_r.
    unfold_real_lat_r. force_r (_, _, _, Vint v).
    iFrame "ASM". iSplit; et.
    iIntros "[PT ->]". steps_r. hss_r. steps_r.
    
    inline_r.
    unfold_real_lat_r. force_r (_, _, _, _).
    iFrame "PT". iSplit; et.
    iIntros "[PT ->]". steps_r. hss_r. steps_r.

    force_l; iFrame "PT"; steps_l.
    sch_yield_rr.
    Unshelve. all: try exact 0.
    sch_yield_l; steps_l; clear v; rename _q into v.
    steps_r; inline_r.
    unfold_real_lat_r. force_r (_, _, _, _).
    iFrame. iSplit; et.
    iIntros "[PT ->]". steps_r. hss_r. steps_r.
    steps_r; inline_r.
    unfold_real_lat_r. force_r (_, _, _, _).
    iFrame. iSplit; et.
    iIntros "[PT ->]". steps_r. hss_r. steps_r.

    force_l; iFrame "PT"; steps_l.
    steps_r.
    sch_yield_rr.
    steps_r.
    sch_yield_l; steps_l.
    step.
    iSplit; done.
  Unshelve. all: eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { split; ss; iIntros "_"; iSplit; eauto. }
    { eapply faa2_simF. }
  Qed.
End FaaIA. End FaaIA.
