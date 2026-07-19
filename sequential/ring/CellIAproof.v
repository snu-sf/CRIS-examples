From CRIS.common Require Import CRIS.
Require Import ImpPrelude.
Require Import CellHeader CellI CellA.

(* Simulation Proof *)
Module CellIA. Section CellIA.
  Import CellA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.
  Context (sp_s : specmap) (idx : nat).

  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
       ∃ vany v,
        ⌜st_tgt = {[CellI.v_cv idx # vany]}⌝
        ∗ ((cell idx v ∗ auth idx v) ∨ (⌜vany = v↑⌝ ∗ pending idx ∗ auth idx v)))%I.

  (* Definitions of two Cell modules *)
  Local Definition CellAMod := (CellA.t idx sp_s).
  Local Definition CellIMod := (CellI.t idx).

  Lemma simF_get : ISim.sim_fun open CellAMod CellIMod Ist (fid (CellHdr.get idx)).
  Proof using.
    cStartFunSim. rewrite /CellI.get.

    (* SRC: precondition *)
    cStepsS. iDestruct "ASM" as "(% & % & C)". subst.
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. cSimpl. rename _q into v.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    (* TGT: return the value of Cell with [idx] *)
    cStepsT. cStepsT.

    (* SRC: take cSteps *)
    cForcesS. iSplitL "C". { eauto. }

    cStep. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma simF_set : ISim.sim_fun open CellAMod CellIMod Ist (fid (CellHdr.set idx)).
  Proof using.
    cStartFunSim. rewrite /CellI.set.

    (* SRC: precondition *)
    cStepsS. destruct _q as [v v'].
    iDestruct "ASM" as "(% & % & [P|C])"; subst.
    { (* A case with a resource [P: pending idx] *)
      iDestruct "IST" as (vany v0) "(% & [(C & A)|(% & P' & A)])"; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }
      des; subst. cSimpl.

      iMod (cell_auth_set with "C A") as "(C & A)".

      (* TGT, SRC: take cSteps *)
      cStepsT.
      cForcesS. iSplitL "C". { eauto. } cStepsS.
      (* Prove the IST *)
      cStep.
      iSplit; eauto.
      iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
    }

    (* A case with a resource [C: cell idx v] *)
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. cSimpl.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".

    (* TGT, SRC: take cSteps *)
    cStepsT.
    cForcesS. iSplitL "C". { eauto. } cStepsS.

    (* Prove the IST *)
    cStep.
    iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  (*SLOW*)Qed.

  Theorem sim : ISim.t open CellAMod CellIMod (CellA.init_cond idx) Ist.
  Proof.
    cStartModSim.
    - iIntros "IC". iDestruct "IC" as (v) "(C & A)".
      repeat iExists _. iSplit; eauto. iLeft. iFrame.
    - eapply simF_get; eauto.
    - eapply simF_set; eauto.
  Qed.
End CellIA. End CellIA.
