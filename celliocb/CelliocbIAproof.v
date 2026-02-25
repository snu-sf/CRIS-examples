Require Import CRIS.
Require Import CelliocbHeader CelliocbA CelliocbI.

Local Open Scope nat_scope.

Module CelliocbIA. Section CelliocbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !celliocbGS}.

  Definition Ist : ist_type Σ :=
    (λ st_s st_t, (∃ v, ⌜st_t = {[CelliocbI.v_cv # v↑]}⌝ ∗ auth v))%I.

  Local Definition CelliocbIMod := (CelliocbI.t).
  Local Definition CelliocbAMod := (CelliocbA.t).

  Lemma simF_set :
    ISim.sim_fun open CelliocbAMod CelliocbIMod Ist (fid CelliocbHdr.set).
  Proof using.
    iStartSim. rewrite /CelliocbI.set /set.
  
    (* Take (x:Z) & cell(x) *)
    steps_l. destruct Any.downcast; steps_l; des_ifs.

    (* Call cb() simultaneously *)
    steps_r. 
    call "IST". iIntros "% % % IST". 
    steps_l. steps_r.
    destruct Any.downcast; steps_l; des_ifs.
    rename z into v_new.
    
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
  
  Lemma simF_get : ISim.sim_fun open CelliocbAMod CelliocbIMod Ist (fid CelliocbHdr.get).
  Proof using.
    iStartSim.
    unfold get, CelliocbI.get.

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
  
  Lemma sim : ISim.t open CelliocbAMod CelliocbIMod CelliocbA.init_cond Ist.
  Proof using.
    init_sim.
    - iIntros. iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CelliocbIA. End CelliocbIA.
