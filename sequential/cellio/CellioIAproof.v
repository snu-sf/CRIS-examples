From CRIS.common Require Import CRIS.
From CRIS.cellio Require Import CellioHeader CellioA CellioI CtxHeader.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellioGS}.

  Definition Ist : ist_type Σ :=
    fun st_src st_tgt =>
      (∃ v, ⌜st_tgt = {[CellioI.v_cv # (v↑)]}⌝ ∗ auth v)%I.

  Local Definition CellioI := (CellioI.t).
  Local Definition CellioA := (CellioA.t).

  Lemma simF_set : ISim.sim_fun open CellioA CellioI Ist (fid CellioHdr.set).
  Proof using.
    cStartFunSim. unfold CellioI.set, CellioA.set.

    (* Take (x:Z) & cell(x) *)
    cStepsS. destruct Any.downcast; cStepsS; des_ifs.
    rename _q into v. iRename "ASM" into "CELL".

    (* Call Input() simultaneously *)
    cStepsT.
    cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsT. cStepsS. destruct Any.downcast as [v_new|]; [|cStepsS; ss].
    cStepsT. cStepsS.

    (* Give cell(i) *)
    iDestruct "IST" as (v') "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "CELL AUTH") as "<-".
    iMod (cell_auth_set with "CELL AUTH") as "(CELL & AUTH)".

    cStepsT. cForcesS. iSplitL "CELL"; eauto.

    cStep.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  (*SLOW*)Qed.
  
  Lemma simF_get : ISim.sim_fun open CellioA CellioI Ist (fid CellioHdr.get).
  Proof using.
    cStartFunSim. unfold CellioI.get, CellioA.get.

    (* Take (x:Z) & cell(x) *)
    cStepsS. destruct Any.downcast; cStepsS; des_ifs.
    rename _q into v. iRename "ASM" into "CELL".
    iDestruct "IST" as (v') "(-> & AUTH)".

    iPoseProof (cell_auth_get with "CELL AUTH") as "<-".

    cStepsT. cStepsT.

    (* Give cell(x) *)
    cForcesS. iSplitL "CELL"; eauto.
    
    cStep. iSplit; eauto.
    iExists _. iFrame. eauto.
  (*SLOW*)Qed.
  
  Lemma sim : ISim.t open CellioA CellioI CellioA.init_cond Ist.
  Proof using.
    cStartModSim.
    - iIntros "H". iExists _. iFrame. et.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CellioIA. End CellioIA.
