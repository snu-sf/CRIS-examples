Require Import CRIS.
From CRIS.celliocb Require Import CelliocbHeader CelliocbA MaincbHeader MaincbA MaincbI CtxcbHeader.


Module MaincbIA. Section MaincbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !celliocbGS}.

  Context (sp : specmap).
  Context (sp_foo: sp.1 !! fid CtxcbHdr.foo = None).
  
  Local Notation CelliocbAMod := (CelliocbA.t).
  Local Notation MaincbA := (MaincbA.t sp).
  Local Notation IstFull := (IstProd (IstSB MaincbA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_main : ISim.sim_fun open MaincbA (MaincbI.t ★ CelliocbAMod) IstFull entry.
  Proof using sp_foo.
    cStartFunSim.
    unfold MaincbA.main, MaincbI.main.
    
    (* Take cell(0) *)
    cStepsS.
    iDestruct "ASM" as "[-> ASM]".

    (* Give cell(0) *)
    cStepsT. cInlineT. cStepsT. cForcesT. iFrame.
    
    (* Inline input_stdin() *)
    cStepsT. cInlineT. cStepsT. unfold MaincbI.input_stdin. 
    
    (* trigger IO together *)
    cStep. rename ret into i. 
    cStepsT. cStepsS. rewrite sp_foo.

    (* Take cell(i) *)
    cInlineT. rewrite /get. cStepsT. cForcesT. iFrame. cStepsT.

    (* cCall foo together *)
    cCall "IST". iIntros "% % % IST".

    (* TGT : handle set(input_db) *)
    cStepsS. cStepsT.
    destruct Any.downcast; cStepsS; des_ifs. cStepsT.
    
    (* TGT : inline set *)
    cInlineT. cStepsT. cForcesT.

    (* TGT : give cell i *)
    iFrame. cStepsT.
    
    (* TGT : inline input_db *)
    cInlineT. rewrite /MaincbI.input_db. cStepsT.

    (* handle IO together *)
    cStep. cStepsT.

    (* TGT : inline get *)
    cInlineT.
    cStepsT. unfold get. cForceT ret0.
    
    (* TGT : get cell ret *)
    cForcesT. iFrame.

    cStepsT. cStepsS. 
    
    (* handle IO together *)
    cStep. cStepsS. cStepsT. cForcesS. iSplit; et. cStep. iFrame; et. 
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MaincbA (MaincbI.t ★ CelliocbAMod) emp IstFull.
  Proof using sp_foo.
    cStartModSim.
    { iIntros "_". unfold IstFull, IstProd. repeat (iExists ∅). ss. } 
    { eapply simF_main; eauto. }
  Qed.
End MaincbIA. End MaincbIA.
