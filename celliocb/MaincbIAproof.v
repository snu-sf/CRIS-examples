Require Import CRIS.
From CRIS.celliocb Require Import CelliocbHeader CelliocbA MaincbHeader MaincbA MaincbI CtxcbHeader.


Module MaincbIA. Section MaincbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !celliocbGS}.

  Context (sp : specmap).
  Context (sp_foo: sp.1 !! fid CtxcbHdr.foo = None).
  Context (sp_cb: sp.1 !! fid MaincbHdr.input_cb = None).
  
  Local Notation CelliocbAMod := (CelliocbA.t).
  Local Notation MaincbA := (MaincbA.t sp).
  Local Notation IstFull := (IstProd (IstSB MaincbA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_cb : ISim.sim_fun open MaincbA (MaincbI.t ★ CelliocbAMod) IstFull (fid MaincbHdr.input_cb).
  Proof using.
    cStartFunSim. 
    cStepsS. cStepsT. unfold MaincbA.input_cb, MaincbI.input_cb.
    cStep. cStep. cStep. 
    iSplit; et.
  Qed. 

  Lemma simF_main : ISim.sim_fun open MaincbA (MaincbI.t ★ CelliocbAMod) IstFull entry.
  Proof using sp_foo sp_cb.
    cStartFunSim.
    unfold MaincbA.main, MaincbI.main.
    
    (* Take cell(0) *)
    cStepsS.
    iDestruct "ASM" as "[-> ASM]".

    (* Give cell(0) *)
    cStepsT. cInlineT. cStepsT. cForcesT. iFrame.
    
    (* sync callback *)
    cStepsT. cInlineT. cStepsT. unfold MaincbI.input_cb.
    rewrite sp_cb. cInlineS. cStepsS. unfold MaincbA.input_cb.
    cStep. cStep. cStepsS. cStepsT. 
     
    
    (* sync foo *)
    rewrite sp_foo.
    cCall "IST". iIntros "% % % IST".

    (* TGT : inline get *)
    cStepsT. cInlineT.
    cStepsT. unfold get. cForceT ret0.
    
    (* TGT : get cell ret *)
    cForcesT. iFrame.

    cStepsT. cStepsS. 
    
    (* sync print *)
    cStep. cStepsS. cStepsT. cForcesS. iSplit; et. cStep. iFrame; et. 
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MaincbA (MaincbI.t ★ CelliocbAMod) emp IstFull.
  Proof using sp_foo sp_cb.
    cStartModSim.
    { iIntros "_". unfold IstFull, IstProd. repeat (iExists ∅). ss. }
    { eapply simF_cb; eauto. }  
    { eapply simF_main; eauto. }
  Qed.
End MaincbIA. End MaincbIA.
