Require Import CRIS.
Require Import CelliocbHeader CelliocbA CelliocbI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CelliocbIA. Section CelliocbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{_celliocbG: !celliocbG}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    λ _ st_src st_tgt,
      (∃ v, ⌜st_tgt = [(CelliocbI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Definition CelliocbI := (CelliocbI.t).
  Local Definition CelliocbA := (CelliocbA.t).

  Lemma simF_set : HSim.sim_fun open CelliocbA CelliocbI CelliocbA.InitCond Ist (Some CelliocbHdr.set).
  Proof using.
    init_simF.
  
    (* Take (x:Z) & cell(x) *)
    steps_l. hss.
    rename q into cb. rename q0 into v.

    (* Call cb() simultaneously *)
    steps_r. hss. steps_r.
    call "IST".
    steps_l. hss. rename q into v_new.
    
    (* Give cell(i) *)
    iDestruct "IST" as (v') "(% & AUTH)". subst.
    iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
    iMod (cell_auth_set _ v_new with "ASM AUTH") as "(C & A)".

    force_l. iFrame.
    
    steps_r. hss. steps_r. steps_l.

    step.
    iSplit; eauto.
    iExists v_new. iFrame; hss.
  (*SLOW*)Qed.
  
  Lemma simF_get : HSim.sim_fun open CelliocbA CelliocbI CelliocbA.InitCond Ist (Some CelliocbHdr.get).
  Proof using.
    init_simF.

    (* Take (x:Z) & cell(x) *)
    steps_l. 
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
    steps_r. hss. steps_r.

    (* Give cell(x) *)
    forces_l. iFrame. 
    
    steps_l.

    step. iSplit; eauto.
    iExists _. iFrame; eauto.
  (*SLOW*)Qed.
  
  Lemma sim : HSim.t open CelliocbA CelliocbI CelliocbA.InitCond Ist.
  Proof using.
    init_sim.
    - split; et. iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CelliocbIA. End CelliocbIA.
