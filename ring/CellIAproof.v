Require Import CRIS.

Require Import ImpPrelude.
Require Import CellHeader CellI CellA.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Simulation Proof *)
Module CellIA. Section CellIA.
  Import CellAS.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_cellG: !cellG}.

  Variable idx : nat.

  (* A spec table *)
  Context (Sp_s : string → option fspec).

  Definition Ist : nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    (λ _ st_src st_tgt,
       ∃ vany v,
        ⌜st_tgt = [(CellI.v_cv idx, vany)]⌝
        ∗ ((cell idx v ∗ auth idx v)
          ∨ (⌜vany = v↑⌝ ∗ pending idx ∗ auth idx v)))%I.

  (* Definitions of two Cell modules *)
  Local Definition CellA := (CellA.t idx Sp_s).
  Local Definition CellI := (CellI.t idx).

  (*************)

  Lemma simF_get : HSim.sim_fun open CellA CellI Ist (CellHdr.get idx).
  Proof using _cellG.
    init_simF.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((% & C) & %)". subst. hss.
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss. rename q into v.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    (* TGT: return the value of Cell with [idx] *)
    steps_r. hss. steps_r.

    (* SRC: take steps *)
    forces_l. iSplitL "C". { eauto. } steps_l.

    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma simF_set:
    HSim.sim_fun open CellA CellI Ist (CellHdr.set idx).
  Proof using _cellG.
    init_simF.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((% & [P|C]) & %)";
      subst; hss; rename q1 into v, q2 into v'; unfold Ist.
    { (* A case with a resource [P: pending idx] *)
      iDestruct "IST" as (vany v0) "(% & [(C & A)|(% & P' & A)])"; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }
      des; subst. hss.

      iMod (cell_auth_set with "C A") as "(C & A)".

      (* TGT, SRC: take steps *)
      steps_r. hss.
      forces_l. iSplitL "C". { eauto. } steps_l.

      (* Prove the IST *)
      step.
      iSplit; eauto.
      iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
    }

    (* A case with a resource [C: cell idx v] *)
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".

    (* TGT, SRC: take steps *)
    steps_r. hss.
    forces_l. iSplitL "C". { eauto. } steps_l.

    (* Prove the IST *)
    step.
    iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  (*SLOW*)Qed.

  Theorem sim : HSim.t open CellA CellI (CellA.InitCond idx) Ist.
  Proof.
    init_sim.
    - iIntros "H". iDestruct "H" as (v) "(C & A)".
      repeat iExists _. iSplit; eauto. iLeft. iFrame.
    - eapply simF_get; eauto.
    - eapply simF_set; eauto.
  Qed.

End CellIA. End CellIA.
