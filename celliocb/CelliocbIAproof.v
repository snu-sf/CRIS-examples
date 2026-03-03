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
    cStartFunSim. rewrite /CelliocbI.set /set.
  
    (* Take (x:Z) & cell(x) *)
    cStepsS. destruct Any.downcast; cStepsS; des_ifs.

    (* Call cb() simultaneously *)
    cStepsT. 
    cCall "IST". iIntros "% % % IST". 
    cStepsS. cStepsT.
    destruct Any.downcast; cStepsS; des_ifs.
    rename z into v_new.
    
    (* Give cell(i) *)
    iDestruct "IST" as (v') "(% & AUTH)". subst.
    iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
    iMod (cell_auth_set _ v_new with "ASM AUTH") as "(C & A)".

    cForceS. iFrame.
    
    cStepsT. cSimpl. cStepsT. cStepsS.

    cStep.
    iSplit; eauto.
    iExists v_new. iFrame; cSimpl.
  (*SLOW*)Qed.
  
  Lemma simF_get : ISim.sim_fun open CelliocbAMod CelliocbIMod Ist (fid CelliocbHdr.get).
  Proof using.
    cStartFunSim.
    unfold get, CelliocbI.get.

    (* Take (x:Z) & cell(x) *)
    cStepsS. 
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
    cStepsT. cSimpl. cStepsT.

    (* Give cell(x) *)
    cForcesS. iFrame. 
    
    cStepsS.

    cStep. iSplit; eauto.
    iExists _. iFrame; eauto.
  (*SLOW*)Qed.
  
  Lemma sim : ISim.t open CelliocbAMod CelliocbIMod CelliocbA.init_cond Ist.
  Proof using.
    cStartModSim.
    - iIntros. iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CelliocbIA. End CelliocbIA.
