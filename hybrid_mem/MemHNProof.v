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
    cStartFunSim. rewrite /HybMem.alloc /NonDetMem.alloc.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    iDestruct "IST" as (? ? ? ?) "%". des; cSimpl. des_ifs; cycle 1.
    { cStepsS. ss. }
    cForceT false. cStepsT.

    cStepsT. cStepsS.
    cStepsS. cForceS _q. cStepsS.

    cStep. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (* SLOW *)Qed.

  Lemma simF_free : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.free).
  Proof using.
    cStartFunSim. rewrite /HybMem.free /NonDetMem.free.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.

    cStepsS. cForceT false. cStepsT. cStepsT.
    cStepsS. cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS. cStepsT. cStep. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.load).
  Proof using.
    cStartFunSim. rewrite /HybMem.load /NonDetMem.load.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.

    cStepsS. cStepsS. cStepsS. 
    cForceT false. cStepsT. cStepsT.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    cStep. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_store : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.store).
  Proof using.
    cStartFunSim. rewrite /HybMem.store /NonDetMem.store.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    iDestruct "IST" as (? ? ? ?) "%". des; cSimpl.

    destruct v.
    cStepsS. cStepsS.
    cForceT false. cStepsT. cStepsT.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    cStep. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.cmp).
  Proof using.
    cStartFunSim. rewrite /HybMem.cmp /NonDetMem.cmp.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    iDestruct "IST" as (? ? ? ?) "%". des; cSimpl.

    destruct v.
    cStepsS. cStepsS.
    cForceT false. cStepsT. cStepsT.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.
    cStep. iSplit; [eauto|].
    iPureIntro. repeat (esplits; eauto).
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.cas).
  Proof using.
    cStartFunSim. rewrite /HybMem.cas /NonDetMem.cas.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }
    cStepsS; cStepsT.

    destruct v. destruct v0.
    cStepsS. cStepsS.
    cForceT false. cStepsT.
    cCall "IST" as (???) "IST". cStepsS. cStepsT.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }

    cStepsS; cStepsT.
    cCall "IST" as (???) "IST". cStepsS. cStepsT.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }

    cStepsS. cStepsT.
    des_ifs; cycle 1.
    { cStepsS. cStepsT. cStep. iSplit; eauto. } 
    cStepsS. cStepsT. 
    cCall "IST" as (???) "IST". cStepsS. cStepsT.
    rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. ss. }

    cStepsS. cStepsT.
    cStep. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open NonDetMem HybMem emp%I IstFull.
  Proof using.
    cStartModSim.
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
      (HybMem, emp%I)
      (NonDetMem, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End MemHN. End MemHN.
