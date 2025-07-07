Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import MainHeader.
From CRIS.cellio Require Import CellioHeader CellioA CellioI MainA MainI CtxHeader CtxA CellioIAproof MainIAproof.

Module CellioAll. Section CellioAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; cellioΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Local Definition irΓ : Γ := **[ir_invΓ; CellioA.irΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ].
  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    apply CellioA.ir_valid.
  Qed.

  Variable CtxA: SMod.t.
  Variable CtxI: HMod.t.
  Variable CtxInitCond : iProp Σ.
  
  Local Definition smod_src : SMod.t := MainA.Mod ☆ CtxA.
  Local Definition sp : string → option fspec := ElimRel.sp_from smod_src.
  Local Definition mod_cancel : HMod.t := SMod.to_hmod sp_none (SMod.cancel smod_src).
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := MainI.t ★ CellioI.t ★ CtxI.
  Local Definition with_trivial_spec body : (option fspec) * fbody  := (Some fspec_trivial, body).
  
  Hypothesis ModulesWF : HMod.wf mod_tgt.
  Hypothesis CtxCorrect: ctx_refines (SMod.to_hmod sp CtxA, CtxInitCond) (CtxI, emp%I).
  Hypothesis inputInCtx : ∃ msk sc input (SCP: incl sc CtxA.(SMod.scopes)),
    alist_find (Some CtxHdr.input) (SMod.fnsems CtxA) = Some (true, msk, sc, with_trivial_spec input).
  Hypothesis fooInCtx : ∃ msk sc foo (SCP: incl sc CtxA.(SMod.scopes)),
    alist_find (Some CtxHdr.foo) (SMod.fnsems CtxA) = Some (true, msk, sc, with_trivial_spec foo).

  Local Definition main_cond : iProp Σ := MainA.main_spec.(precond) tt ()↑ ()↑.
  Local Definition init_cond : iProp Σ := MainA.InitCond ∗ CellioA.InitCond.

  Hypothesis CtxInitCondConsistent:
    ∀ rs, ✓ rs → (Own rs ⊢ init_cond ∗ main_cond) →
    ∃ rs', ✓ rs' ∧ (Own rs' ⊢ init_cond ∗ main_cond ∗ CtxInitCond).

  (* Apply cancellation to linked spec module *)
  Lemma cancel_from_src:
    refines (mod_cancel, ((init_cond ∗ CtxInitCond))%I) 
            (mod_src, init_cond ∗ CtxInitCond)%I.
  Proof.
    eapply Cancel.cancellation.
    - ii; des; subst; inv FIND; admit.
     (* ss. rewrite !eq_rel_dec_correct in H0; des_ifs. *)
    - econs; [refl|]; i; inv NS; des; inv H; des; inv H1;
      rewrite !eq_rel_dec_correct in H2; des_ifs.
    - econs; unfold_hmod; ss; prove_nodup.
  Qed.

  Lemma lib_sp_incl: sp_incl CtxAS.sp sp.
  Proof.
    i. rewrite /CtxAS.sp. unseal CRIS. econs; first prove_nodup.
    destruct inputInCtx, fooInCtx. des. intros ? ?.
    rewrite /sp /sp_from /smod_src /to_sp alist_find_map /o_map //=.
    rewrite !eq_rel_dec_correct. des_ifs.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond ∗ CtxInitCond)%I (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    (* consider identical modules in src/tgt as context (CtxA, CtxA) *)
    rewrite /init_cond /mod_src /smod_src /mod_tgt.
    rewrite !add_interp_comm.
    
    (* solve by transitivity:
      MainI ★ CellioI ⊆ MainI ★ CellioA ⊆ MainA ★ CellioA 
    *)
    etrans; cycle 1.
    { (* CellioI ⊆ctx CellioA *)
      ctxr_drop. ctxr_rotate. ctxr_drop.
      eapply main_adequacy, CellioIA.sim.
      eapply lib_sp_incl.
    }
    etrans; cycle 1.
    { (* MainI ★ CellioA ⊆ MainA *)
      ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply main_adequacy, MainIA.sim.
      eapply lib_sp_incl.
    }

    etrans; cycle 1.
    { (* CtxI ⊆ CtxA *)
      ctxr_rotate. ctxr_drop.
      eapply CtxCorrect.
    }
    
    rewrite /MainIAproof.MainIA.MainA /MainA.t. unseal CRIS.
    eapply ctxr_cond_strengthen.
    iIntros "[[? ?] ?]". iFrame.
  (*SLOW*)Qed.

  Lemma cancel_from_tgt :
    refines (mod_cancel, ((init_cond ∗ CtxInitCond) ∗ main_cond)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_from_src. }
    { eapply src_tgt. }
  Qed.

  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_mod
      (HMod.to_mod mod_cancel src_res)
      (HMod.to_mod mod_tgt tgt_res).
  Proof.
    move: (cancel_from_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit (H ModulesWF).
    clear H; intros [WF H].

    assert (∃ rs, ✓ rs ∧ (Own rs ⊢ init_cond ∗ main_cond)).
    { exists (irΣ ⋅ initial_resource_own_admin). split.
      - apply irΣ_valid.
      - rewrite /init_cond /MainA.InitCond /CellioA.InitCond.
        simplify_res.
        { iDestruct "H12" as "[H2 H3]".
          rewrite /CellioA.auth /main_cond /MainA.main_spec /precond. s.
          rewrite /CellioA.cell. s. iFrame. et.
        }
        all: solve_res.
    }
    des. eapply CtxInitCondConsistent in H1; et. des.

    destruct (H rs'); et.
    { iIntros "H". iPoseProof (H2 with "H") as "[? [? ?]]". iFrame. }
    { des. et. }
  (*SLOW*)Qed.
End CellioAll. End CellioAll.
(* Print Assumptions CellioAll.behavioral_refinement. *)
