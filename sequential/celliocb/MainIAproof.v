From CRIS.common Require Import CRIS.
From CRIS.celliocb Require Import CellioHeader CellioA MainHeader MainA MainI
  CtxHeader.


Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !cellioGS}.

  Context (sp : specmap).
  Context (sp_foo: sp.1 !! fid CtxHdr.foo = None).
  Context (sp_cb: sp.1 !! fid MainHdr.input_cb = None).
  
  Local Notation CellioAMod := (CellioA.t).
  Local Notation MainA := (MainA.t sp).
  Section SIM_FUNS.

    Context `{STATE : !stateGS Σ}.

    Local Definition IstFull : iProp Σ := True%I.

    Lemma simF_cb :
      ⊢ ISim.sim_fun open MainA (MainI.t ★ CellioAMod) IstFull
          (fid MainHdr.input_cb).
    Proof using.
      cStartFunSim. unfold MainA.input_cb, MainI.input_cb.
      cStepS. cStepT. destruct Any.downcast; cStepsS; des_ifs.
      cStepsS. cStepsT. cStep. cStep. cStep. iSplit; et.
    Qed.

    Lemma simF_main :
      ⊢ ISim.sim_fun open MainA (MainI.t ★ CellioAMod) IstFull entry.
    Proof using sp_foo sp_cb.
      cStartFunSim. unfold MainA.main, MainI.main.

      (* Take cell(0) *)
      cStepsS. cSimpl.
      iDestruct "ASM" as "[-> ASM]".

      (* Give cell(0) *)
      cStepsT. cInlineT. cStepsT. cForcesT. iFrame.

      (* sync callback *)
      cStepsT. cInlineT. cStepsT.
      cInlineS. cStepsS. unfold MainA.input_cb.
      cStep. cStep. cStepsS. cStepsT. cSimpl.

      (* sync foo *)
      des_ifs. cCall "IST" as (?) "IST".
      destruct Any.downcast; [|cStepsS; ss].

      (* TGT : inline get *)
      cStepsT. cInlineT.
      cStepsT. unfold get. cForceT ret0.

      (* TGT : get cell ret *)
      cForcesT. iFrame.
      cStepsT. cStepsS.

      (* sync print *)
      cStep. cStepsS. cStepsT. cForcesS. iSplit; et. cStep. iFrame; et.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim : ⊢ ISim.t open MainA (MainI.t ★ CellioAMod).
  Proof using sp_foo sp_cb.
    cStartModSim (fun _ : stateGS Σ => IstFull).
    { done. }
    { iApply simF_cb; eauto. }
    { iApply simF_main; eauto. }
  Qed.
End MainIA. End MainIA.
