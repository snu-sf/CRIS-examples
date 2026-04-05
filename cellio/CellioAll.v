Require Import CRIS Cancel.
Require Import ImpPrelude.
From CRIS.cellio Require Import CellioHeader CellioA CellioI MainA MainI CellioIAproof MainIAproof CtxHeader.

Section CellioAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _CELL: !cellioGS}.

  Variable Ctx : SMod.t.
  Hypothesis ctx_real: SMod.is_real Ctx.
  Hypothesis ctx_mod_wf: Mod.wf (SMod.to_mod ∅ Ctx).
  Hypothesis ctx_cancellable : SMod.cancellable Ctx.
  Hypothesis ctx_has_input: fid CtxHdr.input ∈ dom (SMod.fnsems Ctx).
  Hypothesis ctx_has_foo: fid CtxHdr.foo ∈ dom (SMod.fnsems Ctx).
  Hypothesis ctx_main_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems MainI.t) → False.
  Hypothesis ctx_cellio_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems CellioI.t) → False.
  Hypothesis ctx_main_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes MainI.t) → False.
  Hypothesis ctx_cellio_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes CellioI.t) → False.

  Local Definition Ctx_filtered : SMod.t := SMod.filter (CFilter.msk_filter_out {[MainAS.main]}) (SMod.filter SFilter.msk_filter_out Ctx).
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel (MainA.smod ☆ Ctx_filtered)).
  Local Definition mod_tgt : Mod.t := MainI.t ★ CellioI.t ★ SMod.to_mod ∅ Ctx.

  Local Definition sp : specmap := SMod.sp_from (MainA.smod ☆ Ctx_filtered).
  Local Definition mod_src : Mod.t := SMod.to_mod sp MainA.smod ★ SMod.to_mod ∅ Ctx.

  Local Definition init_cond : iProp Σ :=
    (CellioA.init_cond)%I.

  Lemma sp_input: sp.1 !! fid CtxHdr.input = None.
  Proof.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with.
    assert (FIND: exists x, SMod.fnsems Ctx !! fid CtxHdr.input = Some (Some x)).
    { eapply elem_of_dom in ctx_has_input. inv ctx_has_input. eauto.
      inv ctx_mod_wf. destruct x; eauto.
      destruct (SMod.fnsems Ctx !! fid CtxHdr.input) eqn:FIND; ss.
      inv H. hexploit (wf_fns (fid CtxHdr.input)).
      { rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND //. }
      i. ss. inv H.
    }
    des. rewrite !lookup_fmap FIND. ss. destruct x, p. eauto.
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

  Lemma sp_main: sp.1 !! fid MainAS.main = Some (MainAS.main_spec: fspec_rel).
  Proof.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with. simpl_map.
    destruct (SMod.fnsems Ctx_filtered !! fid MainAS.main) eqn: Lctxf_main; et.
    exfalso. eapply (ctx_main_disj (fid MainAS.main)); rewrite elem_of_dom; et.
    rewrite !lookup_fmap in Lctxf_main.
    destruct (SMod.fnsems _ !! _) eqn: Lctx_main; ss.
  Qed.
  
  (* Apply cancellation to linked spec module *)
  Lemma cancel_src:
    refines
      (mod_src, init_cond)
      (mod_top, init_cond ∗ CellioA.cell 0 ∗ Cancel.init_res)%I.
  Proof.
    etrans.
    { eapply ctxr_refines. ctxr_drop.
      eapply SFilter.smod_filter_intro. }
    etrans.
    { eapply ctxr_refines. ctxr_drop.
      eapply CFilter.smod_filter_intro with (bl:={[MainAS.main]}). }
    etrans.
    { eapply ctxr_refines. ctxr_rotate. ctxr_drop.
      eapply Cancel.cancellation_prepare; et; clarify.
    }
    etrans.
    { eapply ctxr_refines. ctxr_rotate. ctxr_drop.
      eapply Cancel.cancellation_prepare with (sps := sp); et; i; cycle 1.
      { rewrite SFilter.cfilter_comm in H0.
        eapply SFilter.filter_masked; et.
      }
      
      ltac2:(renames H into Lfn, Lsp).
      eapply CFilter.filter_masked; et.
      rewrite lookup_empty in Lsp. apply not_eq_sym, not_eq_None_Some in Lsp.
      destruct Lsp as [? Lsp]. eapply SMod.sp_core_from_add_lookup in Lsp.
      destruct Lsp as [Lsp|Lsp]; des; cycle 1.
      - eapply SMod.sp_core_from_lookup in Lsp0; des.
        rewrite !lookup_fmap in Lsp0.
        destruct (SMod.fnsems Ctx !! _) as [[[? []]|]|] eqn: Lctx_fc; ss; subst.
        eapply ctx_real in Lctx_fc; subst; ss.
      - eapply SMod.sp_core_from_lookup in Lsp; des.
        rewrite lookup_insert_Some in Lsp; des; ss. 
        rewrite lookup_singleton_Some in Lsp1. set_solver.
    }

    rewrite -SMod.to_mod_cancel_add left_id.
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add.
      - r; rewrite /= /MainA.fnsems //; mod_tac ss.
      - eapply CFilter.filter_cancellable, SFilter.filter_cancellable. et.
    }
    { assert (Ce : SMod.fnsems Ctx !! entry = None).
      { eapply not_elem_of_dom. ii. eapply ctx_main_disj; eauto.
        rewrite /MainI.t /MainI.smod /SMod.to_mod /= /Mod.fnsems. set_solver.
      }
      assert (Ht : (SMod.sp_from (MainA.smod ☆ Ctx_filtered)).1 !! entry =
        fsp_some MainAS.main_spec); last (rewrite Ht; clear Ht).
      { rewrite /SMod.sp_from /SMod.sp_core_from.
        rewrite !lookup_omap !lookup_fmap lookup_omap lookup_union_with.
        simpl_map; ss. rewrite !lookup_fmap Ce //.
      }
      eexists _, _; splits.
      { ss; exists tt; split; refl. }
      { iIntros "($ & _ & [_ _])"; eauto. }
      { unfoldPrePost. iIntros (??) "[$ _]". }
    }
  (*SLOW*)Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_tgt, emp%I) (mod_src, init_cond)%I.
  Proof.
    eapply ctxr_refines.
    rewrite /init_cond /mod_src /mod_tgt.
    
    (* solve by transitivity:
      MainI ★ CellioI ⊆ MainI ★ CellioA ⊆ MainA ★ CellioA 
    *)
    etrans.
    { (* CellioI ⊆ctx CellioA *)
      ctxr_drop. ctxr_rotate. ctxr_drop.
      eapply main_adequacy, CellioIA.sim.
    }

    etrans.
    { (* MainI ★ CellioA ⊆ MainA *)
      ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply main_adequacy, MainIA.sim; eauto using sp_input, sp_foo, sp_main.
    }

    etrans.
    { (* reorder *)
      ctxr_rotate. ctxr_drop. refl.
    }
    
    eapply ctxr_consequence.
    iIntros "$".
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines
      (mod_tgt, emp%I)
      (mod_top, init_cond ∗ CellioA.cell 0 ∗ Cancel.init_res)%I.
  Proof.
    etrans.
    { eapply src_tgt. }
    { eapply cancel_src. }
  Qed.

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt. rewrite !assoc comm.
    eapply Mod.add_wf; cycle 2; et.
    { mod_tac. }
    { eapply NoDup_app. esplits.
      - apply ctx_mod_wf.
      - mod_tac.
      - prove_nodup.
    }
    econs.
    - mod_tac.
    - prove_nodup.
  (*SLOW*)Qed.
End CellioAux.

Module CellioAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; cellioΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Lemma behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : cellioGS),
    ∀ (Ctx : SMod.t)
      (ctx_real: SMod.is_real Ctx)
      (ctx_mod_wf: Mod.wf (SMod.to_mod ∅ Ctx))
      (ctx_cancellable : SMod.cancellable Ctx)
      (ctx_has_input: fid CtxHdr.input ∈ dom (SMod.fnsems Ctx))
      (ctx_has_foo: fid CtxHdr.foo ∈ dom (SMod.fnsems Ctx))
      (ctx_main_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems MainI.t) → False)
      (ctx_cellio_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems CellioI.t) → False)
      (ctx_main_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes MainI.t) → False)
      (ctx_cellio_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes CellioI.t) → False),
    ∃ src_res tgt_res,
    refines_lmod
      (Mod.to_lmod (mod_tgt Ctx) tgt_res)
      (Mod.to_lmod (mod_top Ctx) src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "[% [% [% [% ?]]]]".
    iMod cellio_alloc as "[% ?]".
    iExists _, _, _, _, _.
    pose proof top_tgt as Href.
    iStopProof. eapply entails_pointwise; iIntros (res Hres) "R".
    iPoseProof (Own_valid with "R") as "%".
    iPureIntro. i.
    rewrite /refines in Href; hexploit Href; eauto using tgt_wf.
    clear Href; intros [? Href].
    hexploit (Href res); eauto.
    { rewrite Hres. iIntros "((W & $ & $ & $ & $) & $ & $)".
      rewrite {1}winv_split_empty comm //.
    }
    s; i; des; et.
  (*SLOW*)Qed.
End CellioAll.

(* Print Assumptions CellioAll.behavioral_refinement. *)
