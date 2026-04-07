Require Import CRIS.
From CRIS.celliocb Require Import CellioHeader CellioA MainHeader MainA MainI CtxHeader.


Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !cellioGS}.

  Context (sp : specmap).
  Context (sp_foo: sp.1 !! fid CtxHdr.foo = None).
  Context (sp_cb: sp.1 !! fid MainHdr.input_cb = None).
  
  Local Notation CellioAMod := (CellioA.t).
  Local Notation MainA := (MainA.t sp).
  Local Notation IstFull := (IstProd (IstSB MainA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_cb : ISim.sim_fun open MainA (MainI.t ★ CellioAMod) IstFull (fid MainHdr.input_cb).
  Proof using.
    cStartFunSim. unfold MainA.input_cb, MainI.input_cb.
    cStepsS. cStepsT. cStep. cStep. cStep. iSplit; et.
  Qed. 

  Lemma simF_main : ISim.sim_fun open MainA (MainI.t ★ CellioAMod) IstFull entry.
  Proof using sp_foo sp_cb.
    cStartFunSim.
    unfold MainA.main, MainI.main.
    
    (* Take cell(0) *)
    cStepsS.
    iDestruct "ASM" as "[-> ASM]".

    (* Give cell(0) *)
    cStepsT. cInlineT. cStepsT. cForcesT. iFrame.
    
    (* sync callback *)
    cStepsT. cInlineT. cStepsT. unfold MainI.input_cb.
    rewrite sp_cb. cInlineS. cStepsS. unfold MainA.input_cb.
    cStep. cStep. cStepsS. cStepsT. 
     
    
    (* sync foo *)
    rewrite sp_foo.
    cCall "IST" as (???) "IST".

    (* TGT : inline get *)
    cStepsT. cInlineT.
    cStepsT. unfold get. cForceT ret0.
    
    (* TGT : get cell ret *)
    cForcesT. iFrame.

    cStepsT. cStepsS. 
    
    (* sync print *)
    cStep. cStepsS. cStepsT. cForcesS. iSplit; et. cStep. iFrame; et. 
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MainA (MainI.t ★ CellioAMod) emp IstFull.
  Proof using sp_foo sp_cb.
    cStartModSim.
    { iIntros "_". unfold IstFull, IstProd. repeat (iExists ∅). ss. }
    { eapply simF_cb; eauto. }  
    { eapply simF_main; eauto. }
  Qed.
End MainIA. End MainIA.
