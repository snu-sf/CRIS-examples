From CRIS.common Require Import CRIS.
From CRIS.celliocb Require Import CellioHeader CellioA CellioI.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !cellioGS}.

  Section SIM_FUNS.

    Context `{STATE : !stateGS Σ}.

    Definition Ist : iProp Σ :=
      (∃ v, CellioI.v_cv ↦tgt v↑ ∗ auth v)%I.

    Local Definition CellioIMod := (CellioI.t).
    Local Definition CellioAMod := (CellioA.t).

    Lemma simF_set :
      ⊢ ISim.sim_fun open CellioAMod CellioIMod Ist (fid CellioHdr.set).
    Proof using.
      cStartFunSim. rewrite /CellioI.set /set.

      (* Take (x:Z) & cell(x) *)
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs.

      (* Call cb() simultaneously *)
      cStepsT.
      cCall "IST" as (?) "IST".
      cStepsS. cStepsT.
      destruct Any.downcast; cStepsS; des_ifs.
      rename z into v_new.

      (* Give cell(i) *)
      iDestruct "IST" as (v') "(CV & AUTH)".
      iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
      iMod (cell_auth_set _ v_new with "ASM AUTH") as "(C & A)".

      cForceS. iFrame.

      cStepsT. cStepsS.

      cStep.
      iSplit; eauto.
      iExists v_new. iFrame; cSimpl.
    (*SLOW*)Qed.

    Lemma simF_get :
      ⊢ ISim.sim_fun open CellioAMod CellioIMod Ist (fid CellioHdr.get).
    Proof using.
      cStartFunSim. unfold get, CellioI.get. cHideS. cHideT. cHideR.

      (* Take (x:Z) & cell(x) *)
      cStepsS. destruct Any.downcast; cStepsS; des_ifs.
      iDestruct "IST" as (v) "(CV & AUTH)".

      iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
      cStepsT.

      (* Give cell(x) *)
      cForcesS. iFrame.

      cStep. iSplit; first done.
      iExists _. iFrame.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim : CellioA.init_cond ⊢ ISim.t open CellioAMod CellioIMod.
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
