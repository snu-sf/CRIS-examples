Require Import CRIS.
Require Import CellioHeader CellioA CellioI CtxHeader.

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
    iStartSim. unfold CellioI.set, CellioA.set.

    (* Take (x:Z) & cell(x) *)
    steps_l. iDestruct "ASM" as "->". hss.
    ltac2:(renames _q into v). iRename "ASM'" into "CELL".

    (* Call Input() simultaneously *)
    steps_r.
    call "IST". iIntros (ret st_src' st_tgt') "IST".
    steps_r. steps_l. destruct Any.downcast as [v_new|]; [|steps_l; ss]. hss.
    steps_r. steps_l.

    (* Give cell(i) *)
    iDestruct "IST" as (v') "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "CELL AUTH") as "<-".
    iMod (cell_auth_set with "CELL AUTH") as "(CELL & AUTH)".

    forces_l. iSplitL "CELL"; eauto.

    steps_l. forces_l.
    iSplit; eauto.
    steps_r. steps_l.

    step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  (*SLOW*)Qed.
  
  Lemma simF_get : ISim.sim_fun open CellioA CellioI Ist (fid CellioHdr.get).
  Proof using.
    iStartSim. unfold CellioI.get, CellioA.get.

    (* Take (x:Z) & cell(x) *)
    steps_l. iDestruct "ASM" as "->".
    ltac2:(renames _q into v). iRename "ASM'" into "CELL". hss.
    iDestruct "IST" as (v') "(-> & AUTH)".

    iPoseProof (cell_auth_get with "CELL AUTH") as "<-".

    steps_r. hss. steps_r.

    (* Give cell(x) *)
    forces_l. iSplitL "CELL"; eauto.
    
    steps_l. forces_l. iSplit; eauto.

    step. iSplit; eauto.
    iExists _. iFrame. eauto.
  (*SLOW*)Qed.
  
  Lemma sim : ISim.t open CellioA CellioI CellioA.init_cond Ist.
  Proof using.
    init_sim.
    - iIntros "H". iExists _. iFrame. et.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CellioIA. End CellioIA.
