Require Import CRIS.
From CRIS.cellio Require Import CellioHeader CellioA MainA MainI CtxHeader.

Set Implicit Arguments.

Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_cellioG: !cellioG}.

  Definition Ist: alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ st_src st_tgt, emp%I.

  Context (sp: sp_type).
  Context (sp_input: sp CtxHdr.input = None).
  Context (sp_foo: sp CtxHdr.foo = None).
  
  Local Definition CellioA := (CellioA.t).
  Local Definition MainA := (MainA.t sp).
  Local Definition IstFull := (IstProd (IstSB MainA.(Mod.scopes) Ist) IstEq).

  Lemma simF_main:
    ISim.sim_fun open MainA (MainI.t ★ CellioA) MainA.init_cond IstFull None.
  Proof using sp_input sp_foo.
    init_simF.
    
    (* Take cell(0) *)
    steps_l. 
    iDestruct "IST" as "[IST ASM]"; subst.

    steps_r. inline_r.
    (* Give cell(0) *)
    steps_r. forces_r. iSplitL ""; eauto.
    forces_r. iSplitL "ASM"; eauto.

    (* Call Input() simultaneously *)
    steps_r. rewrite sp_input.
    call "IST". 
    {
      iDestruct "IST" as "[-> ->]".
      repeat iExists []. iSplit; eauto;
      repeat unfold_mod; ss;
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    }
    steps_l. steps_r. hss.

    (* Take cell(i) *)
    steps_r. iDestruct "GRT'" as "%". subst. hss.
    
    (* Call Foo.foo() simultaneously *)
    steps_r. rewrite sp_foo.
    call "IST"; eauto.
    steps_l. hss. steps_r. hss. steps_r.

    inline_r.
    (* Give cell(i) *)
    step_r. forces_r. iSplitL ""; eauto.
    forces_r. iSplitL "GRT"; eauto.

    (* Take cell(i) *)
    steps_r. iDestruct "GRT'" as "%". subst. hss.

    (* Call Print(i) simultaneously *)
    steps_r. step.

    steps_l. steps_r. step. eauto.

    Unshelve. all:(exact ()).
  (*SLOW*)Qed.

  Theorem sim :
    ISim.t open MainA (MainI.t ★ CellioA) MainA.init_cond IstFull.
  Proof using sp_input sp_foo.
    init_sim.
    (* - exfalso. revert H. rewrite /MainI.t /CellioA. unseal CRIS; ss. *)
    - eapply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
