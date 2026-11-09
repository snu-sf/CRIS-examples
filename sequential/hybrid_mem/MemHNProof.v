From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.hybrid_mem Require Import MemHdr MemLib HybridMem NonDetMem.

Module MemHN. Section MemHN.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Section SIM_FUNS.
    Context `{STATE : !stateGS Σ}.

    Definition Ist : iProp Σ :=
      (∃ mem : Mem.t,
        NonDetMem.v_mem ↦src mem↑ ∗ HybMem.v_mem ↦tgt mem↑)%I.

    Local Definition NonDetMem := NonDetMem.t.
    Local Definition HybMem := HybMem.t.
    Local Definition IstFull := Ist.

    Lemma simF_alloc :
      ⊢ ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.alloc).
    Proof using.
      cStartFunSim. rewrite /HybMem.alloc /NonDetMem.alloc.
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT.
      iDestruct "IST" as (mem) "[MEMS MEMT]".
      cSimpl. des_ifs; cycle 1.
      { cStepsS. ss. }
      cForceT false. cStepsT. cStepsS.
      cForceS _q. cStepsS.
      cStep. iSplit; first done. iExists _. iFrame.
    (* SLOW *)Qed.

    Lemma simF_free :
      ⊢ ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.free).
    Proof using.
      cStartFunSim. rewrite /HybMem.free /NonDetMem.free.
      cStepsS; cStepsT.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT.
      iDestruct "IST" as (mem) "[MEMS MEMT]". cSimpl.

      cForceT false.
      cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS. cStepsT. rewrite Heq. cStepsT.
      cStep. iSplit; first done. iExists _. iFrame.
    (*SLOW*)Qed.

    Lemma simF_load :
      ⊢ ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.load).
    Proof using.
      cStartFunSim. rewrite /HybMem.load /NonDetMem.load.
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT.
      iDestruct "IST" as (mem) "[MEMS MEMT]". cSimpl.

      cForceT false.
      cStepsS.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite Heq. cStepsT.
      cStep. iSplit; first done. iExists _. iFrame.
    (*SLOW*)Qed.

    Lemma simF_store :
      ⊢ ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.store).
    Proof using.
      cStartFunSim. rewrite /HybMem.store /NonDetMem.store.
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT.
      iDestruct "IST" as (mem) "[MEMS MEMT]". cSimpl.

      destruct v.
      cForceT false.
      cStepsS.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite Heq. cStepsT.
      cStep. iSplit; first done. iExists _. iFrame.
    (*SLOW*)Qed.

    Lemma simF_cmp :
      ⊢ ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.cmp).
    Proof using.
      cStartFunSim. rewrite /HybMem.cmp /NonDetMem.cmp.
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT.
      iDestruct "IST" as (mem) "[MEMS MEMT]". cSimpl.

      destruct v.
      cForceT false.
      cStepsS.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite Heq. cStepsT.
      cStep. iSplit; first done. iExists _. iFrame.
    (*SLOW*)Qed.

    Lemma simF_cas :
      ⊢ ISim.sim_fun open NonDetMem HybMem IstFull (fid MemHdr.cas).
    Proof using.
      cStartFunSim. rewrite /HybMem.cas /NonDetMem.cas.
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }
      cStepsS; cStepsT.

      destruct v. destruct v0.
      cStepsS. cStepsS.
      cForceT false. cStepsT.
      cCall "IST" as (?) "IST". cStepsS. cStepsT.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }

      cStepsS; cStepsT.
      cCall "IST" as (?) "IST". cStepsS. cStepsT.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }

      cStepsS. cStepsT.
      des_ifs; cycle 1.
      { cStepsS. cStepsT. cStep. iSplit; eauto. }
      cStepsS. cStepsT.
      cCall "IST" as (?) "IST". cStepsS. cStepsT.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS. ss. }

      cStepsS. cStepsT.
      cStep. iSplit; eauto.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim : ⊢ ISim.t open NonDetMem HybMem.
  Proof using.
    cStartModSim (fun STATE : stateGS Σ => Ist (STATE := STATE)).
    - iPoseProof (state_init_src_acc _ _ NonDetMem.v_mem with "SRC") as
        (ovs) "(%Hsrc & MEMS & _)".
      { set_solver. }
      iPoseProof (state_init_tgt_acc _ _ HybMem.v_mem with "TGT") as
        (ovt) "(%Htgt & MEMT & _)".
      { set_solver. }
      simpl_map. subst ovs ovt. iExists Mem.empty. iFrame.
    - iApply simF_alloc.
    - iApply simF_free.
    - iApply simF_load.
    - iApply simF_store.
    - iApply simF_cmp.
    - iApply simF_cas.
  (*SLOW*)Qed.

  Lemma ctxr :
    ⊢ ctx_refines HybMem NonDetMem.
  Proof using.
    iApply (main_adequacy HybMem NonDetMem).
    iApply sim.
  Qed.
End MemHN. End MemHN.
