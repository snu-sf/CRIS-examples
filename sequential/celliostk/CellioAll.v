From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.imp_system.mem Require Import MemI MemA MemIAproof.
From CRIS.celliostk Require Import MainHeader CellioHeader CellioA CellioI
  MainA MainI CtxHeader CellioIAproof MainIAproof.

Section CellioAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _CELL: !cellioGS}.
  Context `{_MEM: !memGS}.

  Variable Ctx : SMod.t.
  Hypothesis ctx_real: SMod.is_real Ctx.
  Hypothesis ctx_mod_wf: Mod.wf (SMod.to_mod ∅ Ctx).
  Hypothesis ctx_cancellable : SMod.cancellable Ctx.
  Hypothesis ctx_has_foo: fid CtxHdr.foo ∈ dom (SMod.fnsems Ctx).
  Hypothesis ctx_main_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems MainI.t) → False.
  Hypothesis ctx_cellio_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems CellioI.t) → False.
  Hypothesis ctx_mem_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems (MemI.t [])) → False.
  Hypothesis ctx_main_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes MainI.t) → False.
  Hypothesis ctx_cellio_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes CellioI.t) → False.
  Hypothesis ctx_mem_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes (MemI.t [])) → False.

  Local Definition Ctx_filtered : SMod.t := SMod.filter SFilter.msk_filter_out Ctx.
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel (MainA.smod ☆ Ctx_filtered)).
  Local Definition mod_tgt : Mod.t := MainI.t ★ CellioI.t ★ (MemI.t []) ★ (SMod.to_mod ∅ Ctx).

  Local Definition sp : specmap := SMod.sp_from (MainA.smod ☆ Ctx_filtered).
  Local Definition mod_src : Mod.t := SMod.to_mod sp MainA.smod ★ SMod.to_mod ∅ Ctx.

  Local Definition init_cond : iProp Σ :=
    (MemA.init_cond [])%I.

  Lemma sp_cb: sp.1 !! fid MainHdr.input_cb = None.
  Proof.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with.
    assert (CTXNONE: SMod.fnsems Ctx !! fid MainHdr.input_cb = None).
    { eapply not_elem_of_dom. ii. eapply ctx_main_disj; eauto.
      rewrite /MainI.t /MainI.smod /SMod.to_mod /= /Mod.fnsems. set_solver.
    } 
    des. rewrite !lookup_fmap CTXNONE. ss.
  (*SLOW*)Qed.

  Lemma sp_foo: sp.1 !! fid CtxHdr.foo = None.
  Proof.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with.
    assert (FIND: exists x, SMod.fnsems Ctx !! fid CtxHdr.foo = Some (Some x)).
    { eapply elem_of_dom in ctx_has_foo. inv ctx_has_foo. eauto.
      inv ctx_mod_wf. destruct x; eauto.
      destruct (SMod.fnsems Ctx !! fid CtxHdr.foo) eqn:FIND; ss.
      inv H. hexploit (wf_fns (fid CtxHdr.foo)).
      { rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND //. }
      i. ss. inv H.
    }
    des. rewrite !lookup_fmap FIND. ss. destruct x, p. et.
  (*SLOW*)Qed.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src:
    Cancel.init_res ⊢ refines mod_src mod_top.
  Proof.
    iIntros "Hinit".
    rewrite /mod_src /mod_top.
    iApply refines_trans. iSplitR "Hinit".
    { iApply ctxr_refines. ctxr_drop.
      iApply SFilter.smod_filter_intro. }
    iApply refines_trans. iSplitR "Hinit".
    { iApply ctxr_refines. ctxr_rotate. ctxr_drop.
      iApply Cancel.prepare; et; clarify.
    }

    iApply refines_trans. iSplitR "Hinit".
    { iApply ctxr_refines. ctxr_rotate. ctxr_drop.
      iApply (Cancel.prepare _ sp _); et; i; cycle 1.
      { eapply SFilter.filter_masked; et. }

      ltac2:(renames H into Lfn, Lsp).
      rewrite lookup_empty in Lsp. apply not_eq_sym, not_eq_None_Some in Lsp.
      destruct Lsp as [? Lsp]. eapply SMod.sp_core_from_add_lookup in Lsp.
      destruct Lsp as [Lsp|Lsp]; des; cycle 1.
      - eapply SMod.sp_core_from_lookup in Lsp0; des. rewrite !lookup_fmap in Lsp0.
        destruct (SMod.fnsems Ctx !! _) as [[[? []]|]|] eqn: Lctx_fc; ss; subst.
        eapply ctx_real in Lctx_fc; subst; ss.
      - eapply SMod.sp_core_from_lookup in Lsp; des.
        rewrite lookup_insert_Some in Lsp; des; ss. 
        rewrite lookup_singleton_Some in Lsp1. set_solver.
    }

    rewrite -SMod.to_mod_cancel_add.
    iApply Cancel.cancel.
    { apply SMod.cancellable_add.
      - r; rewrite /= /MainA.fnsems //; mod_tac ss.
      - eapply SFilter.filter_cancellable. et.
    }
    { assert (Ce : SMod.fnsems Ctx !! entry = None).
      { eapply not_elem_of_dom. ii. eapply ctx_main_disj; eauto.
        rewrite /MainI.t /MainI.smod /SMod.to_mod /= /Mod.fnsems. set_solver.
      }
      assert (Ht : (SMod.sp_from (MainA.smod ☆ Ctx_filtered)).1 !! entry = fsp_none).
      { rewrite /SMod.sp_from /SMod.sp_core_from.
        rewrite !lookup_omap !lookup_fmap lookup_omap lookup_union_with.
        simpl_map; ss. rewrite !lookup_fmap Ce //.
      }
      rewrite Ht; clear Ht. ss; exists tt; split; refl.
    }
    { unfoldPrePost. iIntros (??) "$". }
    iDestruct "Hinit" as "(X & Y & Z & $ & $)".
    unfoldPrePost; done.
  (*SLOW*)Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "Hinit".
    iApply ctxr_refines.
    rewrite /init_cond /mod_src /mod_tgt.

    iApply ctxr_trans. iSplitL "Hinit".
    { (* MemI ⊆ctx MemA *)
      do 2 ctxr_drop. ctxr_rotate. ctxr_drop.
      iApply main_adequacy.
      { apply MemIA.sim with (sp:=sp). }
      iFrame.
    }

    (* solve by transitivity:
      MainI ★ CellioI ⊆ MainI ★ CellioA ⊆ MainA ★ CellioA 
    *)
    iApply ctxr_trans. iSplitR.
    { (* CellioI ★ MemA ⊆ctx CellioA ★ MemA *)
      ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
      iApply main_adequacy.
      { apply CellioIA.sim. }
      iEmpIntro.
    }

    rewrite /CellioIAproof.CellioIA.CellioAMod.
    iApply ctxr_trans. iSplitR.
    { (* MainI ★ CellioA ⊆ MainA *)
      ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_drop.
      iApply main_adequacy.
      { apply MainIA.sim; eauto using sp_foo, sp_cb. }
      iEmpIntro.
    }

    iApply ctxr_trans. iSplitR.
    { (* drop & rotate *)
      do 2 ctxr_rotate. do 2 ctxr_drop. iApply elim_module.
    }

    rewrite right_id.
    ctxr_refl.
  (*SLOW*)Qed.

  Lemma top_tgt :
    init_cond ∗ Cancel.init_res ⊢ refines mod_tgt mod_top.
  Proof.
    iIntros "[Hinit Hcancel]".
    iApply refines_trans. iSplitL "Hinit".
    { iApply src_tgt. iFrame. }
    iApply cancel_src. iFrame.
  Qed.

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt. rewrite !assoc comm.
    eapply Mod.add_wf; cycle 2; et.
    { mod_tac. }
    { eapply NoDup_app. esplits.
      - apply ctx_mod_wf.
      - mod_tac.
      - prove_nodup; set_solver.
    }
    econs.
    - mod_tac.
    - prove_nodup; set_solver.
  (*SLOW*)Qed.
End CellioAux.

Module CellioAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Lemma behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : memGS),
    ∀ (Ctx : SMod.t)
      (ctx_real: SMod.is_real Ctx)
      (ctx_mod_wf: Mod.wf (SMod.to_mod ∅ Ctx))
      (ctx_cancellable : SMod.cancellable Ctx)
      (ctx_has_foo: fid CtxHdr.foo ∈ dom (SMod.fnsems Ctx))
      (ctx_main_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems MainI.t) → False)
      (ctx_cellio_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems CellioI.t) → False)
      (ctx_mem_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems (MemI.t [])) → False)
      (ctx_main_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes MainI.t) → False)
      (ctx_cellio_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes CellioI.t) → False)
      (ctx_mem_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes (MemI.t [])) → False),
    ∃ src_res tgt_res,
    refines_lmod
      (Mod.to_lmod (mod_tgt Ctx) tgt_res)
      (Mod.to_lmod (mod_top Ctx) src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV Hinit])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINVempty]".
    iMod mem_alloc as "(% & HMem)".
    iExists _, _, _, _, _.
    iModIntro.
    iIntros (Ctx ctx_real ctx_mod_wf ctx_cancellable ctx_has_foo
      ctx_main_disj ctx_cellio_disj ctx_mem_disj ctx_main_scope_disj
      ctx_cellio_scope_disj ctx_mem_scope_disj).
    iPoseProof (top_tgt Ctx with "[WINV Hinit HMem]") as "REF".
    all: try eassumption.
    { iDestruct "HMem" as "[HMem _]".
      rewrite /init_cond /Cancel.init_res /MemA.init_cond.
      iDestruct "Hinit" as "(H0 & H1 & H2 & H3)". iFrame.
    }
    iAssert (⌜∃ src_res, ✓ src_res /\ refines_lmod
      (Mod.to_lmod (mod_tgt Ctx) ε)
      (Mod.to_lmod (mod_top Ctx) src_res)⌝)%I
      with "[WINVempty REF]" as "%Href".
    { iApply refines_adequacy. { eapply tgt_wf; eassumption. } iFrame. }
    destruct Href as [src_res [_ Href]].
    iPureIntro. exists src_res, ε. exact Href.
  (*SLOW*)Qed.
End CellioAll.

(* Print Assumptions CellioAll.behavioral_refinement. *)
