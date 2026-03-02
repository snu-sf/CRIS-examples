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
    iStartSim. unfold MainI.main, MainA.main.

    (* Take cell(0) *)
    steps_l. iDestruct "ASM" as "[-> CELL]". hss.

    steps_r. inline_r. unfold CellioA.set.
    (* Give cell(0) *)
    steps_r. forces_r. iSplit; et.
    forces_r. iSplitL "CELL"; et.

    (* Call Input() simultaneously *)
    steps_r. rewrite sp_input.
    call "IST". iIntros (ret st_src' st_tgt') "IST".
    steps_l. steps_r. destruct Any.downcast as [v|]; [|steps_l; ss]. hss.

    (* Take cell(i) *)
    steps_r. iDestruct "GRT'" as "<-". hss. iRename "GRT" into "CELL".

    (* Call Foo.foo() simultaneously *)
    steps_r. steps_l. rewrite sp_foo.
    call "IST". iIntros (r1 st_src1 st_tgt1) "IST".
    steps_l. steps_r. destruct Any.downcast; [|steps_l; ss]. hss.
    steps_r. inline_r. unfold CellioA.get.
    (* Give cell(i) *)
    step_r. forces_r. iSplitL ""; eauto.
    forces_r. iSplitL "CELL"; eauto.

    (* Take cell(i) *)
    steps_r. iDestruct "GRT'" as "<-". hss. iRename "GRT" into "CELL".

    (* Call Print(i) simultaneously *)
    steps_r. step.

    forces_l. iSplit; et.
    step. iFrame. ss.

    Unshelve. all:(exact ()).
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MainA (MainI.t ★ CellioA) emp%I IstFull.
  Proof using sp_input sp_foo.
    init_sim.
    - iIntros "_". unfold IstFull, IstProd.
      iExists ∅, ∅, ∅, ∅. ss.
    - eapply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
