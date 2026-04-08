Require Import CRIS.
From CRIS.celliocb Require Import CellioHeader CellioA CellioI.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !cellioGS}.

  Definition Ist : ist_type Σ :=
    (λ st_s st_t, (∃ v, ⌜st_t = {[CellioI.v_cv # v↑]}⌝ ∗ auth v))%I.

  Local Definition CellioIMod := (CellioI.t).
  Local Definition CellioAMod := (CellioA.t).

  Lemma simF_set :
    ISim.sim_fun open CellioAMod CellioIMod Ist (fid CellioHdr.set).
  Proof using.
    cStartFunSim. rewrite /CellioI.set /set.
  
    (* Take (x:Z) & cell(x) *)
    cStepsS. destruct Any.downcast; cStepsS; des_ifs.

    (* Call cb() simultaneously *)
    cStepsT. 
    cCall "IST" as (???) "IST".
    cStepsS. cStepsT.
    destruct Any.downcast; cStepsS; des_ifs.
    rename z into v_new.
    
    (* Give cell(i) *)
    iDestruct "IST" as (v') "(% & AUTH)". subst.
    iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
    iMod (cell_auth_set _ v_new with "ASM AUTH") as "(C & A)".

    cForceS. iFrame.
    
    cStepsT. cStepsT. cStepsS.

    cStep.
    iSplit; eauto.
    iExists v_new. iFrame; cSimpl.
  (*SLOW*)Qed.
  
  Lemma simF_get : ISim.sim_fun open CellioAMod CellioIMod Ist (fid CellioHdr.get).
  Proof using.
    cStartFunSim.
    unfold get, CellioI.get.

    (* Take (x:Z) & cell(x) *)
    cStepsS. 
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM AUTH") as "%"; subst.
    cStepsT. cStepsT.

    (* Give cell(x) *)
    cForcesS. iFrame. 
    
    cStepsS.

    cStep. iSplit; eauto.
    iExists _. iFrame; eauto.
  (*SLOW*)Qed.
  
  Lemma sim : ISim.t open CellioAMod CellioIMod CellioA.init_cond Ist.
  Proof using.
    cStartModSim.
    - iIntros. iExists _. iFrame. eauto.
    - apply simF_set; eauto.
    - apply simF_get; eauto.
  Qed.
End CellioIA. End CellioIA.
