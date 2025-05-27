Require Import CRIS.
Require Import CellioHeader CellioA CellioI.
Require Import CtxA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_cellioG: !cellioG}.

  (* sp for src module *)
  Context (sp_s : string → option fspec).
  Context (CtxInSp : sp_incl CtxAS.sp sp_s).
  
  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ st_src st_tgt,
      (∃ v, ⌜st_tgt = [(CellioI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Definition CellioI := (CellioI.t).
  Local Definition CellioA := (CellioA.t sp_s).

  Lemma simF_set : HSim.sim_fun open CellioA CellioI Ist CellioHdr.set.
  Proof using CtxInSp.
    init_simF.
  
    (* Take (x:Z) & cell(x) *)
    steps_l. iDestruct "ASM" as "->".

    (* Call Input() simultaneously *)
    force_l tt. forces_l. iSplit; first eauto.
    call "IST"; eauto.
    steps_l. iDestruct "ASM" as "->".

    (* Give cell(i) *)
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.
    iMod (cell_auth_set with "ASM' AUTH") as "(C & A)".

    forces_l. iSplitL "C"; eauto.

    steps_r. hss. steps_r. steps_l. forces_l.
    iSplit; eauto.

    step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  (*SLOW*)Qed.
  
  Lemma simF_get : HSim.sim_fun open CellioA CellioI Ist CellioHdr.get.
  Proof using CtxInSp.
    init_simF.

    (* Take (x:Z) & cell(x) *)
    steps_l. iDestruct "ASM" as "->".
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.

    steps_r. hss. steps_r.

    (* Give cell(x) *)
    forces_l. iSplitL "ASM'"; eauto.
    
    steps_l. forces_l. iSplit; eauto.

    step. iSplit; eauto.
    iExists _. iFrame. eauto.
  (*SLOW*)Qed.
  
  Lemma sim : HSim.t open CellioA CellioI CellioA.InitCond Ist.
  Proof using CtxInSp.
    init_sim.
    - iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CellioIA. End CellioIA.
