Require Import CRIS Cancel.
Require Import ImpPrelude.
From CRIS.cellio Require Import CellioHeader CellioA CellioI MainA MainI CellioIAproof MainIAproof CtxHeader.

Module CellioAll. Section CellioAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; cellioΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Local Definition irΓ : Γ := **[ir_invΓ; CellioA.irΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ].
  Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    apply CellioA.ir_valid.
  Qed.

  Variable CtxI: SMod.t.
  Hypothesis ctx_real: real_smod CtxI.
  Hypothesis ctx_mod_wf: Mod.wf (SMod.to_mod sp_none CtxI).
  Hypothesis ctx_smod_wf: SMod.wf CtxI.
  Hypothesis ctx_has_input: In (Some CtxHdr.input) (map fst (SMod.fnsems CtxI)).
  Hypothesis ctx_has_foo: In (Some CtxHdr.foo) (map fst (SMod.fnsems CtxI)).
  Hypothesis ctx_main_disj:
    ∀ fno, In fno (map fst (SMod.fnsems CtxI)) → In fno (map fst (Mod.fnsems MainI.t)) → False.
  Hypothesis ctx_cellio_disj:
    ∀ fno, In fno (map fst (SMod.fnsems CtxI)) → In fno (map fst (Mod.fnsems CellioI.t)) → False.
  Hypothesis ctx_main_scope_disj:
    ∀ mn, In mn (SMod.scopes CtxI) → In mn (Mod.scopes MainI.t) → False.
  Hypothesis ctx_cellio_scope_disj:
    ∀ mn, In mn (SMod.scopes CtxI) → In mn (Mod.scopes CellioI.t) → False.

  Local Definition smod_src : SMod.t := MainA.smod ☆ CtxI.
  Local Definition mod_top : Mod.t := SMod.to_mod sp_none (SMod.cancel smod_src).
  Local Definition mod_tgt : Mod.t := MainI.t ★ CellioI.t ★ (SMod.to_mod sp_none CtxI).

  Local Definition sp : sp_type := sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition init_cond : iProp Σ :=
    winv (⊤, ⊤) ∗ MainA.init_cond ∗ CellioA.init_cond.

  Lemma sp_input: sp CtxHdr.input = None.
  Proof.
    rewrite /sp /sp_from /to_sp /smod_src. s.
    rewrite !alist_find_map_snd.
    destruct (alist_find _ _) as [[[[? ?] ?] [? ?]]| ] eqn: E; ss.
    - exploit (ctx_real (Some CtxHdr.input)); et.
    - assert (HAS:= ctx_has_input). eapply in_map_iff in HAS.
      des. destruct x. ss. subst.
      exfalso. eapply alist_find_none in E; et.
  (*SLOW*)Qed.

  Lemma sp_foo: sp CtxHdr.foo = None.
  Proof.
    rewrite /sp /sp_from /to_sp /smod_src. s.
    rewrite !alist_find_map_snd.
    destruct (alist_find _ _) as [[[[? ?] ?] [? ?]]| ] eqn: E; ss.
    - exploit (ctx_real (Some CtxHdr.foo)); et.
    - assert (HAS:= ctx_has_foo). eapply in_map_iff in HAS.
      des. destruct x. ss. subst.
      exfalso. eapply alist_find_none in E; et.
  (*SLOW*)Qed.
  
  (* Apply cancellation to linked spec module *)
  Lemma cancel_src:
    refines (mod_top, init_cond) 
            (mod_src, init_cond).
  Proof using ctx_main_disj ctx_mod_wf ctx_real ctx_smod_wf.
    eapply Cancel.cancellation; et.
    - rewrite /smod_src. ii. destruct fno; ss.
      + eapply ctx_smod_wf; et.
      + inv FIND. et.
    - split; try refl.
      i. r in NS. des. r in NS. des.
      rewrite /sp /smod_src /sp_from /to_sp. s.
      rewrite !alist_find_map_snd.
      destruct (alist_find (Some fn) _) eqn: E; s.
      + destruct p as [[[img0 msk0] scp0] [fsp0 bd0]].
        exploit ctx_real; et. i. subst.
        eapply ctx_smod_wf in E. rewrite E; et.
        s. refl.
      + eapply fspec_bot_strongest.
    - destruct ctx_mod_wf. econs; ss.
      econs.
      + repeat (rewrite map_map; setoid_rewrite fst_map_snd).
        ii. eapply ctx_main_disj; et.
        unfold_mod. s. et.
      + revert wf_fns.
        repeat (rewrite map_map; setoid_rewrite fst_map_snd). et.
  (*SLOW*)Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond)%I (mod_tgt, emp%I).
  Proof using ctx_has_foo ctx_has_input ctx_mod_wf ctx_real ctx_smod_wf.
    eapply ctxr_refines.
    
    rewrite /init_cond /mod_src /smod_src /mod_tgt.
    rewrite !add_interp_comm.
    
    (* solve by transitivity:
      MainI ★ CellioI ⊆ MainI ★ CellioA ⊆ MainA ★ CellioA 
    *)
    etrans; cycle 1.
    { (* CellioI ⊆ctx CellioA *)
      ctxr_drop. ctxr_rotate. ctxr_drop.
      eapply main_adequacy, CellioIA.sim; eauto using sp_input, sp_foo.
    }

    etrans; cycle 1.
    { (* MainI ★ CellioA ⊆ MainA *)
      ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply main_adequacy, MainIA.sim; eauto using sp_input, sp_foo.
    }

    etrans; cycle 1.
    { (* CtxI ⊆ CtxA *)
      ctxr_rotate. ctxr_drop.
      erewrite <-(@real_smod_ignores_sp _ CtxI sp); et. refl.
    }
    
    rewrite /MainIAproof.MainIA.MainA /MainA.t. unseal CRIS.
    eapply ctxr_cond_strengthen.
    iIntros "[? ?]". iFrame.
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    revert_until CtxI. rewrite /mod_tgt /MainI.t /CellioI.t. unseal CRIS. i.
    econs; s.
    - prove_nodup.
      + rewrite map_map in H. setoid_rewrite fst_map_snd in H. et.
      + rewrite map_map in H. setoid_rewrite fst_map_snd in H. et.
      + rewrite map_map in H. setoid_rewrite fst_map_snd in H. et.
      + eapply ctx_mod_wf.
    - prove_nodup.
      + eapply ctx_cellio_scope_disj; et.
      + eapply ctx_mod_wf.
  (*SLOW*)Qed.

  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ init_cond).
  Proof using.
    exists (irΣ ⋅ ir_own_admin). split.
    { apply irΣ_valid. }
    simplify_res.
    { rewrite make_own_admin; iFrame.
      iDestruct "H12" as "[H2 H3]". iFrame.
    }
    all: solve_res.
  Qed.
  
  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    move: (top_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H; eauto using tgt_wf. clear H; intros [WF H].
    assert (IV:= init_cond_valid). des.
    destruct (H rs); des; et.
    rewrite IV0 /init_cond {1}winv_split_empty. iIntros "[[? ?] ?]". iFrame; done.
  (*SLOW*)Qed.
End CellioAll. End CellioAll.
(* Print Assumptions CellioAll.behavioral_refinement. *)
