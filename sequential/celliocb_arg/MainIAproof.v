From CRIS.common Require Import CRIS.
From CRIS.celliocb_arg Require Import CellioHeader CellioA MainHeader CtxHeader
  MainA MainI.

Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !cellioGS}.

  Context (sp : specmap).
  Context (sp_foo : sp.1 !! fid CtxHdr.foo = None).
  Context (sp_cb : sp.1 !! fid MainHdr.input_cb = None).

  Local Notation CellioAMod := CellioA.t.
  Local Notation MainAMod := (MainA.t sp).
  Local Definition IstFull (STATE : stateGS Σ) : iProp Σ :=
    state_eq (list_to_set MainA.scopes) STATE.

  Lemma simF_cb :
    ⊢ ISim.sim_fun open MainAMod (MainI.t ★ CellioAMod) IstFull
        (fid MainHdr.input_cb).
  Proof using.
    clear sp_foo sp_cb.
    cStartFunSim. unfold MainA.input_cb, MainI.input_cb.
    rewrite /IstFull.
    cStepS. cStepT. destruct Any.downcast; cStepsS; cStepsT; des_ifs.
    all: try (exfalso;
      change (bool_decide (scope k ∈ ["Main"]) = true) in Heq;
      change (bool_decide (scope k ∈ ["Main"]) = false) in Heq0;
      congruence).
    all: try (cStepsS; ss).
    cShowS. cShowT. rewrite !vis_trigger.
    iApply wsim_sget_eq.
    { apply bool_decide_eq_true in Heq. rewrite /MainA.scopes in Heq. set_solver. }
    iFrame "IST". iIntros (value) "IST".
    cStepsS. cStepsT. destruct Any.downcast; cStepsS; cStepsT; des_ifs.
    all: try (rewrite /MainA.scopes /MainI.scopes in *; congruence).
    all: try (cStepsS; ss).
    cShowS. cShowT. rewrite !vis_trigger.
    iApply wsim_sput_eq.
    { apply bool_decide_eq_true in Heq. rewrite /MainA.scopes in Heq. set_solver. }
    iFrame "IST". iIntros "IST".
    cStepsS. cStepsT. cStep. iSplit; first done. iFrame.
  Qed.

  Lemma simF_main :
    ⊢ ISim.sim_fun open MainAMod (MainI.t ★ CellioAMod) IstFull entry.
  Proof using sp_foo sp_cb.
    cStartFunSim. unfold MainA.main, MainI.main.

    (* Take cell(0) from Main's entry precondition. *)
    cStepsS. cSimpl.
    iDestruct "ASM" as "[-> ASM]".

    (* Give cell(0) to the abstract Cell.set operation. *)
    cStepsT. cInlineT. cStepsT. cForcesT. iFrame.

    (* Cellio forwards Main's state key to the same callback. *)
    cStepsT. cStepsS.
    cCall "IST" as (?) "IST".
    destruct Any.downcast; [|cStepsS; ss].
    cStepsT. cStepsS.

    (* Continue with the same surrounding context call. *)
    cShowS. rewrite sp_foo. cStepsS.
    des_ifs. cCall "IST" as (?) "IST".
    destruct Any.downcast; [|cStepsS; ss].

    (* Inline Cell.get on the implementation side. *)
    cStepsT. cInlineT.
    cStepsT. unfold CellioA.get. cForceT z.

    (* Recover the callback result retained by Cellio.set. *)
    cForcesT. iFrame.
    cStepsT. cStepsS.

    (* Read Main.count and print the same pair. *)
    cStepsS. cStepsT. cShowS. cShowT. rewrite /IstFull.
    iApply wsim_sget_eq.
    { rewrite /MainA.scopes /MainI.v_count /=. set_solver. }
    iFrame "IST". iIntros (count) "IST".
    cStepsS. cStepsT.
    destruct Any.downcast; [|cStepsS; ss].
    cStepsS. cStepsT.
    cStep. cStepsS. cStepsT. cForcesS. iSplit; et.
    cStep. iSplit; first done.
    iFrame; et.
  (*SLOW*)Qed.

  Lemma sim : ⊢ ISim.t open MainAMod (MainI.t ★ CellioAMod) IstFull.
  Proof using sp_foo sp_cb.
    cStartModSim.
    - vm_compute.
      apply submseteq_cons. apply submseteq_skip. apply submseteq_nil.
    - iEval (rewrite /MainI.t /MainI.smod /CellioA.t /CellioA.smod
        /SMod.to_mod /=) in "TGT".
      iEval (rewrite state_init_tgt_union; last set_solver) in "TGT".
      iDestruct "TGT" as "[_ TGT]".
      iApply (state_eq_init with "SRC TGT").
      rewrite /MainA.scopes /MainA.smod /MainI.t /MainI.smod
        /CellioA.t /CellioA.smod /SMod.to_mod /=.
      simpl_map. done.
    - iApply simF_cb; eauto.
    - iApply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
