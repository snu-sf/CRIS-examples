Require Import CRIS.
Require Import CellioHeader CellioA MainHeader MainA MainI CtxA CtxA.

Set Implicit Arguments.

Module MainIA. Section MainIA.
  Import CellioA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_cellioG: !cellioG}.

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ st_src st_tgt, emp%I.

  Context (sp_s: string -> option fspec).
  Context (CtxInSp: sp_incl CtxAS.sp sp_s). (* Specs of Ctxrary functions *)

  Local Definition CellioA := (CellioA.t sp_s).
  Local Definition MainA := (MainA.t sp_s).
  Local Definition IstFull := (IstProd (IstSB MainA.(HMod.scopes) Ist) IstEq).

  Lemma simF_main:
    HSim.sim_fun open MainA (MainI.t ★ CellioA) IstFull MainHdr.main.
  Proof using CtxInSp.
    init_simF.
    
    (* Take cell(0) *)
    steps_l; iDestruct "ASM" as "[ASM %]"; subst.

    inline_r.
    (* Give cell(0) *)
    steps_r. forces_r. iSplitL ""; eauto.
    forces_r. iSplitL "ASM"; eauto.

    (* Call Input() simultaneously *)
    steps_r. forces_l. iSplitL "GRT"; eauto.
    call "IST"; eauto.
    steps_l. forces_r. iSplitL "ASM"; eauto.
    steps_r. hss.

    (* Take cell(i) *)
    steps_r. iDestruct "GRT'" as "%". subst. hss.
    
    (* Call Foo.foo() simultaneously *)
    steps_l. steps_r. forces_l. iSplitL ""; eauto.
    call "IST"; eauto.
    steps_l. iDestruct "ASM" as "%". subst. hss. steps_r. hss. steps_r.

    inline_r.
    (* Give cell(i) *)
    step_r. forces_r. iSplitL ""; eauto.
    forces_r. iSplitL "GRT"; eauto.

    (* Take cell(i) *)
    steps_r. iDestruct "GRT'" as "%". subst. hss.

    (* Call Print(i) simultaneously *)
    steps_r. step.

    steps_l. forces_l.
    iSplitL ""; eauto.

    steps_r. step. iFrame. eauto.

    Unshelve. all:(exact ()).
  (*SLOW*)Qed.

  Theorem sim :
    HSim.t open MainA (MainI.t ★ CellioA) MainA.InitCond IstFull.
  Proof using CtxInSp.
    init_sim.
    - iIntros "_". repeat iExists []. iSplit; eauto.
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    - eapply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
