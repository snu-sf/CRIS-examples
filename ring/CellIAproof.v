Require Import CRIS.

Require Import ImpPrelude.
Require Import CellHeader CellI CellA.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Simulation Proof *)
Module CellIA. Section CellIA.
  Import CellAS.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!cellG}.

  Variable idx : nat.

  Context (Sp_s : sp_type).

  Definition Ist : alist key Any.t -> alist key Any.t -> iProp Σ :=
    (λ st_src st_tgt,
       ∃ vany v,
        ⌜st_tgt = [(CellI.v_cv idx, vany)]⌝
        ∗ ((cell idx v ∗ auth idx v) ∨ (⌜vany = v↑⌝ ∗ pending idx ∗ auth idx v)))%I.

  (* Definitions of two Cell modules *)
  Local Definition CellAMod := (CellA.t idx Sp_s).
  Local Definition CellIMod := (CellI.t idx).

  (*************)

  Lemma simF_get : ISim.sim_fun open CellAMod CellIMod (CellA.init_cond idx) Ist (Some (CellHdr.get idx)).
  Proof using.
    init_simF.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((% & C) & %)". subst. hss.
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss. rename _q into v.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    (* TGT: return the value of Cell with [idx] *)
    steps_r. hss. steps_r.

    (* SRC: take steps *)
    forces_l. iSplitL "C". { eauto. }
    steps_l. steps_r.

    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma simF_set:
    ISim.sim_fun open CellAMod CellIMod True%I Ist (Some (CellHdr.set idx)).
  Proof using.
    init_simF.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((% & [P|C]) & %)";
      subst; hss; rename _q1 into v, _q2 into v'; unfold Ist.
    { (* A case with a resource [P: pending idx] *)
      iDestruct "IST" as (vany v0) "(% & [(C & A)|(% & P' & A)])"; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }
      des; subst. hss.

      iMod (cell_auth_set with "C A") as "(C & A)".

      (* TGT, SRC: take steps *)
      steps_r. hss.
      forces_l. iSplitL "C". { eauto. } steps_l.
      (* Prove the IST *)
      steps_r. step.
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

  Theorem sim : ISim.t open CellAMod CellIMod (CellA.init_cond idx) Ist.
  Proof.
    init_sim.
    - split; eauto. iIntros "IC". iDestruct "IC" as (v) "(C & A)".
      iModIntro. repeat iExists _. iSplit; eauto. iLeft. iFrame.
    - eapply simF_get; eauto.
    - eapply simF_set; eauto.
  Qed.

End CellIA. End CellIA.
