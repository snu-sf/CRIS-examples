Require Import CRIS.
From CRIS.cellio Require Import CellioHeader CellioA MainA MainI CtxHeader.

Set Implicit Arguments.

Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellioGS}.

  Context (sp: specmap).
  Context (sp_start: sp.1 !! (funid MainAS.main) = Some (MainAS.main_spec: fspec_rel)).
  Context (sp_input: sp.1 !! (fid CtxHdr.input) = None).
  Context (sp_foo: sp.1 !! (fid CtxHdr.foo) = None).

  Local Definition CellioA := (CellioA.t).
  Local Definition MainA := (MainA.t sp).
  Local Definition IstFull := (IstProd (IstSB MainA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_start : ISim.sim_fun open MainA (MainI.t ★ CellioA) IstFull entry.
  Proof using sp_start.
    cStartFunSim. unfold MainI.start, MainA.start.
    cStepsS. rewrite sp_start. cStepsS. cForceS _q. cStepsS. cForceS arg. cStepsS.
    cForceS. iFrame. cStepsS. cStepsT. cCall "IST" as (? ? ?) "IST".
    cStepsS. cForcesS. iSplit; et. cStepsT. cStep. iSplit; et.
  Qed.
  
  Lemma simF_main : ISim.sim_fun open MainA (MainI.t ★ CellioA) IstFull (funid MainAS.main).
  Proof using sp_input sp_foo.
    cStartFunSim. unfold MainI.main, MainA.main.

    (* Take cell(0) *)
    cStepsS. iDestruct "ASM" as "[-> CELL]".

    cStepsT. cInlineT.
    (* Give cell(0) *)
    cStepsT. cForcesT. iSplitL "CELL"; et.

    (* Call Input() simultaneously *)
    cStepsT. rewrite sp_input.
    cCall "IST" as (ret st_src st_tgt) "IST".
    destruct Any.downcast as [v|]; [|cStepsS; ss].

    (* Take cell(i) *)
    cStepsT. iRename "GRT" into "CELL".

    (* Call Foo.foo() simultaneously *)
    cStepsT. cStepsS. rewrite sp_foo.
    cCall "IST" as (r1 st_src st_tgt) "IST".
    destruct Any.downcast; [|cStepsS; ss].
    cStepsT. cInlineT.
    (* Give cell(i) *)
    cStepsT. cForcesT. iSplitL "CELL"; eauto.

    (* Take cell(i) *)
    cStepsT. iRename "GRT" into "CELL".

    (* Call Print(i) simultaneously *)
    cStepsT. cStepsS. cStep.

    cForcesS. iSplit; et.
    cStep. iFrame. ss.

    Unshelve. all:(exact ()).
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MainA (MainI.t ★ CellioA) emp%I IstFull.
  Proof using sp_start sp_input sp_foo.
    cStartModSim.
    - iIntros "_". unfold IstFull, IstProd.
      iExists ∅, ∅, ∅, ∅. ss.
    - eapply simF_start; eauto.
    - eapply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
