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
  Local Definition IstFull (_ : stateGS Σ) : iProp Σ :=
    (∃ count : Z,
      MainA.v_count ↦src count↑ ∗ MainI.v_count ↦tgt count↑)%I.

  Lemma simF_cb :
    ⊢ ISim.sim_fun open MainAMod (MainI.t ★ CellioAMod) IstFull
        (fid MainHdr.input_cb).
  Proof using.
    cStartFunSim. unfold MainA.input_cb, MainI.input_cb.
    iDestruct "IST" as (count) "[COUNTS COUNTT]".
    cStepS. cStepT. destruct Any.downcast; cStepsS; des_ifs.
    cStepsS. cStepsT.
    cStep. iSplit; first done.
    iExists (count + z)%Z. iFrame.
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

    (* Keep input_cb(2) and its count update on both sides. *)
    cStepsT. cInlineT. cStepsT.
    cInlineS. cStepsS. unfold MainA.input_cb.
    iDestruct "IST" as (count) "[COUNTS COUNTT]".
    cStepsS. cStepsT.
    iAssert (IstFull _)%I with "[COUNTS COUNTT]" as "IST".
    { iExists (count + 2)%Z. iFrame. }
    cSimpl.

    (* Continue with the same surrounding context call. *)
    des_ifs. cCall "IST" as (?) "IST".
    destruct Any.downcast; [|cStepsS; ss].

    (* Inline Cell.get on the implementation side. *)
    cStepsT. cInlineT.
    cStepsT. unfold CellioA.get. cForceT (count + 2)%Z.

    (* Recover the value stored by input_cb(2). *)
    cForcesT. iFrame.
    cStepsT. cStepsS.

    (* Read Main.count and print the same pair. *)
    iDestruct "IST" as (count') "[COUNTS COUNTT]".
    cStepsS. cStepsT.
    cStep. cStepsS. cStepsT. cForcesS. iSplit; et.
    cStep. iSplit; first done.
    iExists count'. iFrame; et.
  (*SLOW*)Qed.

  Lemma sim : ⊢ ISim.t open MainAMod (MainI.t ★ CellioAMod) IstFull.
  Proof using sp_foo sp_cb.
    cStartModSim.
    - vm_compute.
      apply submseteq_cons. apply submseteq_skip. apply submseteq_nil.
    - iPoseProof (state_init_src_acc _ _ MainA.v_count with "SRC") as
        (src_count) "(%Hsrc & COUNTS & _)".
      { set_solver. }
      iPoseProof (state_init_tgt_acc _ _ MainI.v_count with "TGT") as
        (tgt_count) "(%Htgt & COUNTT & _)".
      { set_solver. }
      simpl_map. subst src_count tgt_count. iExists 0%Z. iFrame.
    - iApply simF_cb; eauto.
    - iApply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
