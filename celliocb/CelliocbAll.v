Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import MaincbHeader.
Require Import 
  CelliocbHeader CelliocbA CelliocbI MaincbA MaincbI CtxcbHeader CelliocbIAproof MaincbIAproof.

Section CelliocbAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _CELL: !celliocbGS}.

  Variable CtxcbI : SMod.t.
  Hypothesis ctx_real: SMod.is_real CtxcbI.
  Hypothesis ctx_mod_wf: Mod.wf (SMod.to_mod ∅ CtxcbI).
  Hypothesis ctx_cancellable : SMod.cancellable CtxcbI.
  Hypothesis ctx_has_foo: fid CtxcbHdr.foo ∈ dom (SMod.fnsems CtxcbI).
  Hypothesis ctx_main_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems CtxcbI) → fno ∈ dom (Mod.fnsems MaincbI.t) → False.
  Hypothesis ctx_cellio_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems CtxcbI) → fno ∈ dom (Mod.fnsems CelliocbI.t) → False.
  Hypothesis ctx_main_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes CtxcbI) → mn ∈ (Mod.scopes MaincbI.t) → False.
  Hypothesis ctx_cellio_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes CtxcbI) → mn ∈ (Mod.scopes CelliocbI.t) → False.

  Local Definition smod_src : SMod.t := MaincbA.smod ☆ CtxcbI.
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).

  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.
  Local Definition mod_tgt : Mod.t := MaincbI.t ★ CelliocbI.t ★ (SMod.to_mod sp CtxcbI).

  Local Definition init_cond : iProp Σ :=
    (CelliocbA.init_cond)%I.

  Lemma sp_foo: sp.1 !! fid CtxcbHdr.foo = None.
  Proof.
    rewrite /sp /SMod.conc_sp_from /= /smod_src /SMod.sp_core_from.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with.
    assert (FIND: exists x, SMod.fnsems CtxcbI !! fid CtxcbHdr.foo = Some (Some x)).
    { eapply elem_of_dom in ctx_has_foo. inv ctx_has_foo. eauto.
      inv ctx_mod_wf. destruct x; eauto.
      destruct (SMod.fnsems CtxcbI !! fid CtxcbHdr.foo) eqn:FIND; ss.
      inv H. hexploit (wf_fns (fid CtxcbHdr.foo)).
      { rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND //. }
      i. ss. inv H.
    }
    des. rewrite FIND. ss. destruct x, p. r in ctx_real. hexploit ctx_real; eauto.
  (*SLOW*)Qed.

  Lemma sp_cb: sp.1 !! fid MaincbHdr.input_cb = None.
  Proof.
    rewrite /sp /SMod.conc_sp_from /= /smod_src /SMod.sp_core_from.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with.
    assert (CTXNONE: SMod.fnsems CtxcbI !! fid MaincbHdr.input_cb = None).
    { eapply not_elem_of_dom. ii. eapply ctx_main_disj; eauto.
      rewrite /MaincbI.t /MaincbI.smod /SMod.to_mod /= /Mod.fnsems. set_solver.
    } 
    des. rewrite CTXNONE. ss.
  (*SLOW*)Qed.


  (* Apply cancellation to linked spec module *)
  Lemma cancel_src:
    refines (mod_top, init_cond ∗ CelliocbA.cell 0 ∗ Cancel.init_res)%I
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation; et.
    { apply SMod.cancellable_add; r; rewrite /= /MaincbA.fnsems //; mod_tac ss. }
    { assert (Ce : SMod.fnsems CtxcbI !! entry = None).
      { eapply not_elem_of_dom. ii. eapply ctx_main_disj; eauto.
        rewrite /MaincbI.t /MaincbI.smod /SMod.to_mod /= /Mod.fnsems. set_solver.
      }
      assert (Ht : (SMod.conc_sp_from smod_src).1 !! entry =
        fsp_some MaincbA.main_spec); last (rewrite Ht; clear Ht).
      { rewrite /SMod.conc_sp_from /SMod.sp_core_from.
        rewrite !lookup_omap !lookup_fmap lookup_omap lookup_union_with.
        simpl_map; ss. rewrite Ce //.
      }
      eexists _, _; splits.
      { ss; exists tt; split; refl. }
      { iIntros "($ & _ & [_ _])"; eauto. }
      { unfoldPrePost. iIntros (??) "[$ _]". }
    }
  (*SLOW*)Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond)%I (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /init_cond /mod_src /smod_src /mod_tgt.
    rewrite !SMod.to_mod_add.
    
    (* solve by transitivity:
      MaincbI ★ CelliocbI ⊆ MaincbI ★ CelliocbA ⊆ MaincbA ★ CelliocbA 
    *)
    etrans; cycle 1.
    { (* CelliocbI ⊆ctx CelliocbA *)
      ctxr_drop. ctxr_rotate. ctxr_drop.
      eapply main_adequacy, CelliocbIA.sim.
    }

    etrans; cycle 1.
    { (* MaincbI ★ CelliocbA ⊆ MaincbA *)
      ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply main_adequacy, MaincbIA.sim; eauto using sp_foo, sp_cb.
    }

    etrans; cycle 1.
    { (* CtxcbI ⊆ CtxcbI *)
      ctxr_rotate. ctxr_drop. refl.
    }

    eapply ctxr_cond_strengthen.
    iIntros "$".
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond ∗ CelliocbA.cell 0 ∗ Cancel.init_res)%I
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt; eapply Mod.add_wf.
    { econs; eauto; [mod_tac|prove_nodup]. }
    { eapply Mod.add_wf.
      { econs; eauto; [mod_tac|prove_nodup]. }
      { inv ctx_mod_wf. econs.
        { ii. destruct (SMod.fnsems CtxcbI !! i) eqn: FIND.
          { rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND /= in H. inv H.
            destruct o; ss. hexploit (wf_fns i); eauto.
            rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND //.
          }
          { rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND /= in H. inv H. }
        }
        { rewrite /SMod.to_mod /= in wf_scopes. rewrite /SMod.to_mod //. }
      }
      { ii. rewrite /Mod.fnsems /SMod.to_mod /= dom_fmap in H0. eauto. }
      { eapply NoDup_app. esplits; eauto.
        { prove_nodup. }
        { inv ctx_mod_wf. rewrite /Mod.scopes /SMod.to_mod /= in wf_scopes.
          rewrite /Mod.scopes /SMod.to_mod //.
        }
      }
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { eapply NoDup_app. esplits; eauto.
      { prove_nodup. }
      { ii. ss. rewrite sorting.merge_sort_Permutation in H0. set_solver. }
      { ss. rewrite sorting.merge_sort_Permutation.
        eapply NoDup_cons. esplits; eauto.
        { ii. eapply ctx_cellio_disj; eauto. set_solver. }
        { inv ctx_mod_wf. rewrite /Mod.scopes /SMod.to_mod /= in wf_scopes.
          rewrite /Mod.scopes /SMod.to_mod //.
        }
      }
    }
  (*SLOW*)Qed.
End CelliocbAux.

Module CelliocbAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; celliocbΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Lemma behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : celliocbGS),
    ∀ (CtxcbI : SMod.t)
      (ctx_real: SMod.is_real CtxcbI)
      (ctx_mod_wf: Mod.wf (SMod.to_mod ∅ CtxcbI))
      (ctx_cancellable : SMod.cancellable CtxcbI)
      (ctx_has_foo: fid CtxcbHdr.foo ∈ dom (SMod.fnsems CtxcbI))
      (ctx_main_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems CtxcbI) → fno ∈ dom (Mod.fnsems MaincbI.t) → False)
      (ctx_cellio_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems CtxcbI) → fno ∈ dom (Mod.fnsems CelliocbI.t) → False)
      (ctx_main_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes CtxcbI) → mn ∈ (Mod.scopes MaincbI.t) → False)
      (ctx_cellio_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes CtxcbI) → mn ∈ (Mod.scopes CelliocbI.t) → False),
    ∃ src_res tgt_res,
    refines_lmod
      (Mod.to_lmod (mod_top CtxcbI) src_res)
      (Mod.to_lmod (mod_tgt CtxcbI) tgt_res).
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
End CelliocbAll.

(* Print Assumptions CelliocbAll.behavioral_refinement. *)
