From CRIS.common Require Import CRIS.
From CRIS.cellio Require Import CellioHeader CellioA CellioI CtxHeader.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellioGS}.

  Section SIM_FUNS.

    Context `{STATE : !stateGS Σ}.

    Definition Ist : iProp Σ :=
      (∃ v, CellioI.v_cv ↦tgt v↑ ∗ auth v)%I.

    Local Definition CellioI := (CellioI.t).
    Local Definition CellioA := (CellioA.t).

    Lemma simF_set :
      ⊢ ISim.sim_fun open CellioA CellioI Ist (fid CellioHdr.set).
    Proof using.
      cStartFunSim. unfold CellioI.set, CellioA.set.

      (* Take (x:Z) & cell(x) *)
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs.
      rename _q into v. iRename "ASM" into "CELL".

      (* Call Input() simultaneously *)
      cStepsT.
      cCall "IST" as (ret) "IST".
      cStepsT. cStepsS. destruct Any.downcast as [v_new|]; [|cStepsS; ss].
      cStepsT. cStepsS.

      (* Give cell(i) *)
      iDestruct "IST" as (v') "(CV & AUTH)".

      iPoseProof (cell_auth_get with "CELL AUTH") as "<-".
      iMod (cell_auth_set with "CELL AUTH") as "(CELL & AUTH)".

      cStepsT. cForcesS. iSplitL "CELL"; eauto.

      cStep.
      iSplit; first done.
      iExists _. iFrame.
    (*SLOW*)Qed.

    Lemma simF_get :
      ⊢ ISim.sim_fun open CellioA CellioI Ist (fid CellioHdr.get).
    Proof using.
      cStartFunSim. unfold CellioI.get, CellioA.get.

      (* Take (x:Z) & cell(x) *)
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs.
      rename _q into v. iRename "ASM" into "CELL".
      iDestruct "IST" as (v') "(CV & AUTH)".

      iPoseProof (cell_auth_get with "CELL AUTH") as "<-".

      cStepsT.

      (* Give cell(x) *)
      cForcesS. iSplitL "CELL"; eauto.

      cStep. iSplit; first done.
      iExists _. iFrame.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim : CellioA.init_cond ⊢ ISim.t open CellioA CellioI.
  Proof using.
    cStartModSim (fun STATE : stateGS Σ => Ist (STATE := STATE)).
    - iPoseProof (state_init_tgt_acc _ _ CellioI.v_cv with "TGT") as
        (ov) "(%Hcv & CV & _)".
      { set_solver. }
      simpl_map. subst ov. iExists 0%Z. iFrame.
    - iApply simF_set.
    - iApply simF_get.
  Qed.
End CellioIA. End CellioIA.
