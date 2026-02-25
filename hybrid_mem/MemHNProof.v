From CRIS Require Import CRIS ImpPrelude.
Require Import MemHdr MemLib HybridMem NonDetMem.

Module MemHN. Section MemHN.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      (∃ (mem: Mem.t),
      ⌜st_src = {[NonDetMem.v_mem # mem↑]} ∧ st_tgt = {[HybMem.v_mem # mem↑]}⌝)%I.

  Local Definition NonDetMem := NonDetMem.t.
  Local Definition HybMem := HybMem.t.
  Local Definition IstFull := (IstProd (IstSB NonDetMem.(Mod.scopes) Ist) IstEq).

  Lemma simF_alloc : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.alloc).
  Proof using.
    iStartSim. rewrite /HybMem.alloc /NonDetMem.alloc.
    steps_l. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l. steps_r. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "%". des; hss. des_ifs; cycle 1.
    { steps_l. ss. }
    force_r false. steps_r. hss.

    steps_r. steps_l. hss.
    steps_l. force_l _q. steps_l.

    step. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (* SLOW *)Qed.

  Lemma simF_free : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.free).
  Proof using.
    iStartSim. rewrite /HybMem.free /NonDetMem.free.
    steps_l. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "%". des.

    steps_l. hss. force_r false. steps_r. hss. steps_r.
    steps_l. hss. steps_l. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l. steps_r. step. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.load).
  Proof using.
    iStartSim. rewrite /HybMem.load /NonDetMem.load.
    steps_l. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "%". des.

    steps_l. hss. steps_l. hss. steps_l. 
    force_r false. steps_r. hss. steps_r.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    step. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_store : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.store).
  Proof using.
    iStartSim. rewrite /HybMem.store /NonDetMem.store.
    steps_l. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "%". des; hss.

    destruct v.
    steps_l. hss. steps_l.
    force_r false. steps_r. hss. steps_r.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    step. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.cmp).
  Proof using.
    iStartSim. rewrite /HybMem.cmp /NonDetMem.cmp.
    steps_l. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "%". des; hss.

    destruct v.
    steps_l. hss. steps_l.
    force_r false. steps_r. hss. steps_r.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.
    step. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.cas).
  Proof using.
    iStartSim. rewrite /HybMem.cas /NonDetMem.cas.
    steps_l. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }
    steps_l; steps_r.

    destruct v. destruct v0.
    steps_l. hss. steps_l.
    force_r false. steps_r.
    call "IST". iIntros (???) "IST". steps_l. steps_r.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }

    steps_l; steps_r.
    call "IST". iIntros (???) "IST". steps_l. steps_r.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }

    steps_l. steps_r.
    des_ifs; cycle 1.
    { steps_l. steps_r. step. iSplit; eauto. } 
    steps_l. steps_r. 
    call "IST". iIntros (???) "IST". steps_l. steps_r.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { steps_l. ss. }

    steps_l. steps_r.
    step. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open NonDetMem HybMem emp%I IstFull.
  Proof using.
    init_sim.
    - rewrite /IstFull /HybMem /NonDetMem. unfold_mod. s. 
      iIntros "_". iPureIntro. repeat (esplits; ss).
      + instantiate (1 := ∅). instantiate (1 := Mem.empty). ss.
      + ss.
    - apply simF_alloc.
    - apply simF_free.
    - apply simF_load.
    - apply simF_store.
    - apply simF_cmp.
    - apply simF_cas.
  (*SLOW*)Qed.

  Lemma ctxr :
    ctx_refines
      (NonDetMem, emp%I)
      (HybMem, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End MemHN. End MemHN.
