Require Import CRIS.
Require Import CelliocbHeader CelliocbA CelliocbI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CelliocbIA. Section CelliocbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{_celliocbG: !celliocbG}.

  (* sp for src module *)
  Context (sp_s : sp_type).
  
  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ st_src st_tgt,
      (∃ v, ⌜st_tgt = [(CelliocbI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Definition CelliocbI := (CelliocbI.t).
  Local Definition CelliocbA := (CelliocbA.t).

  Lemma simF_set : HSim.sim_fun open CelliocbA CelliocbI CelliocbA.InitCond Ist (Some CelliocbHdr.set).
  Proof.
    init_simF.
  
    (* Take (x:Z) & cell(x) *)
    steps_l. hss. iDestruct "ASM" as "<-". 
    rename q1 into cb. rename q2 into v.

    (* Call cb() simultaneously *)
    steps_r. hss. steps_r.
    call "IST".
    steps_l.
    
    (* Give cell(i) *)
    iDestruct "IST" as (v') "(% & AUTH)". subst.
    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.
    iMod (cell_auth_set with "ASM' AUTH") as "(C & A)".

    force_l. iFrame.
    
    steps_r. hss. steps_r. steps_l. forces_l.
    iSplit; eauto.

    step.
    iSplit; eauto.
    iExists _. iFrame. eauto.
  (*SLOW*)Qed.
  
  Lemma simF_get : HSim.sim_fun open CelliocbA CelliocbI CelliocbA.InitCond Ist (Some CelliocbHdr.get).
  Proof.
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
  
  Lemma sim : HSim.t open CelliocbA CelliocbI CelliocbA.InitCond Ist.
  Proof.
    init_sim.
    - split; et. iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CelliocbIA. End CelliocbIA.
