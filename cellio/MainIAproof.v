Require Import CRIS.
From CRIS.cellio Require Import CellioHeader CellioA MainA MainI CtxHeader.

Set Implicit Arguments.

Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellioGS}.

  Context (sp: specmap).
  Context (sp_input: sp.1 !! (fid CtxHdr.input) = None).
  Context (sp_foo: sp.1 !! (fid CtxHdr.foo) = None).

  Local Definition CellioA := (CellioA.t).
  Local Definition MainA := (MainA.t sp).
  Local Definition IstFull := (IstProd (IstSB MainA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_main : ISim.sim_fun open MainA (MainI.t ★ CellioA) IstFull entry.
  Proof using sp_input sp_foo.
    cStartFunSim. unfold MainI.main, MainA.main.

    (* Take cell(0) *)
    cStepsS. iDestruct "ASM" as "[-> CELL]". cSimpl.

    cStepsT. cInlineT. unfold CellioA.set.
    (* Give cell(0) *)
    cStepsT. cForcesT. iSplit; et.
    cForcesT. iSplitL "CELL"; et.

    (* Call Input() simultaneously *)
    cStepsT. rewrite sp_input.
    cCall "IST". iIntros (ret st_src' st_tgt') "IST".
    cStepsS. cStepsT. destruct Any.downcast as [v|]; [|cStepsS; ss]. cSimpl.

    (* Take cell(i) *)
    cStepsT. iDestruct "GRT'" as "<-". cSimpl. iRename "GRT" into "CELL".

    (* Call Foo.foo() simultaneously *)
    cStepsT. cStepsS. rewrite sp_foo.
    cCall "IST". iIntros (r1 st_src1 st_tgt1) "IST".
    cStepsS. cStepsT. destruct Any.downcast; [|cStepsS; ss]. cSimpl.
    cStepsT. cInlineT. unfold CellioA.get.
    (* Give cell(i) *)
    cStepT. cForcesT. iSplitL ""; eauto.
    cForcesT. iSplitL "CELL"; eauto.

    (* Take cell(i) *)
    cStepsT. iDestruct "GRT'" as "<-". cSimpl. iRename "GRT" into "CELL".

    (* Call Print(i) simultaneously *)
    cStepsT. cStep.

    cForcesS. iSplit; et.
    cStep. iFrame. ss.

    Unshelve. all:(exact ()).
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MainA (MainI.t ★ CellioA) emp%I IstFull.
  Proof using sp_input sp_foo.
    cStartModSim.
    - iIntros "_". unfold IstFull, IstProd.
      iExists ∅, ∅, ∅, ∅. ss.
    - eapply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
