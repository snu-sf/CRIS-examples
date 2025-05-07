Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CellioHeader MainHeader.
Require Import CellioA CellioI MainA MainI CtxA.
Require Import CellioIAproof MainIAproof.

Module CellioAll. Section CellioAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; cellioΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Local Definition irΓ : Γ := **[ir_invΓ 1; CellioA.irΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ 1].
  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    apply CellioA.ir_valid.
  Qed.

  Variable CtxA: SMod.t.
  Variable CtxI: HMod.t.
  Variable CtxInitCond : iProp Σ.
  
  Local Definition smod_src : SMod.t := MainA.Mod ☆ CtxA.
  Local Definition sp : string → option fspec := sp_from smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := MainI.t ★ CellioI.t ★ CtxI.
  Local Definition with_trivial_spec body := {|fsb_fspec := fspec_trivial; fsb_body := body|}.
  
  Hypothesis ModulesWF : HMod.wf mod_tgt.
  Hypothesis CtxCorrect: ctx_refines (SMod.to_hmod sp CtxA, CtxInitCond) (CtxI, emp%I).
  Hypothesis inputInCtx : ∃ msk sc input (SCP: incl sc CtxA.(SMod.scopes)),
    alist_find CtxHdr.input (SMod.fnsems CtxA) = Some (msk, sc, with_trivial_spec input).
  Hypothesis fooInCtx : ∃ msk sc foo (SCP: incl sc CtxA.(SMod.scopes)),
    alist_find CtxHdr.foo (SMod.fnsems CtxA) = Some (msk, sc, with_trivial_spec foo).

  Local Definition main_fsp : fspec := fspec_trivial.
  Local Definition init_cond : iProp Σ := MainA.InitCond ∗ CellioA.InitCond.

  Hypothesis CtxInitCondConsistent:
    ∀ rs, ✓ rs → (Own rs ⊢ init_cond) →
    ∃ rs', ✓ rs' ∧ (Own rs' ⊢ init_cond ∗ CtxInitCond).

  (* Apply cancellation to linked spec module *)
  Lemma cancel_from_src :
    refines (mod_cancel, ((init_cond ∗ CtxInitCond) ∗ main_fsp.(precond) tt tt↑ tt↑)%I) 
            (mod_src, init_cond ∗ CtxInitCond)%I.
  Proof. eapply cancellation; try by econs. i. iIntros "%POST". iPureIntro. des; eauto. Qed.

  Lemma lib_sp_incl: sp_incl CtxAS.sp sp.
  Proof.
    i. rewrite /CtxAS.sp. unseal CRIS. econs; first prove_nodup.
    destruct inputInCtx, fooInCtx. des.
    ii; rewrite -FIND /sp /sp_from /smod_src //=. des_ifs; ss; des_ifs.
    { rewrite eq_rel_dec_correct in Heq0. des_ifs.
      rewrite /to_sp alist_find_map /o_map. des_ifs.
    }
    { rewrite eq_rel_dec_correct in Heq1. des_ifs.
      rewrite /to_sp alist_find_map /o_map. des_ifs.
    }
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
    refines (mod_cancel, ((init_cond ∗ CtxInitCond) ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
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

    assert (∃ rs, ✓ rs ∧ (Own rs ⊢ init_cond)).
    { exists (irΣ ⋅ initial_resource_own_admin). split.
      - apply irΣ_valid.
      - rewrite /init_cond /MainA.InitCond /CellioA.InitCond.
        simplify_res.
        { iDestruct "H12" as "[H2 H3]". et. }
        all: solve_res.
    }
    des. eapply CtxInitCondConsistent in H1; et. des.
    
    destruct (H rs'); et.
    { iIntros "H". iPoseProof (H2 with "H") as "H". iFrame. et. }
    { des. et. }
  (*SLOW*)Qed.
End CellioAll. End CellioAll.
(* Print Assumptions CellioAll.behavioral_refinement. *)
