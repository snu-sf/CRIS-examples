Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import MaincbHeader.
From CRIS.celliocb Require Import 
  CelliocbHeader CelliocbA CelliocbI MaincbA MaincbI CtxcbHeader CtxcbA CelliocbIAproof MaincbIAproof.

Module CelliocbAll. Section CelliocbAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; celliocbΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Local Definition irΓ : Γ := **[ir_invΓ; CelliocbA.irΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ].
  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    apply CelliocbA.ir_valid.
  Qed.

  Variable CtxcbA: SMod.t.
  (* Variable CtxcbI: HMod.t. *)
  Variable CtxcbInitCond : iProp Σ.
  
  Local Definition smod_src : SMod.t := MaincbA.Mod ☆ CtxcbA.
  Local Definition sp : string → option fspec := ElimRel.sp_from smod_src.
  Local Definition mod_cancel : HMod.t := SMod.to_hmod sp_none (SMod.cancel smod_src).
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition Ctxcb : HMod.t := (SMod.to_hmod sp CtxcbA).
  Local Definition mod_tgt : HMod.t := MaincbI.t ★ CelliocbI.t ★ Ctxcb.
  
  (* It may be possible weakening Hyp about SRC, TGT to Ctx *)
  Hypothesis ModulesWF : HMod.wf mod_tgt.
  Hypothesis fooInCtx : ∃ msk sc foo_body (SCP: incl sc CtxcbA.(SMod.scopes)),
    alist_find (Some CtxcbHdr.foo) (SMod.fnsems CtxcbA) = Some (true, msk, sc, (None, foo_body)).
  (* Need for cancellation with unkown context *)
  Hypothesis SModWF : ElimRel.smod_wf smod_src. 
  Hypothesis SPWF : ElimRel.valid_sp smod_src sp.
  Hypothesis HModWF : HMod.wf mod_cancel.
  
  Local Definition init_cond : iProp Σ := MaincbA.InitCond ∗ CelliocbA.InitCond.

  Hypothesis CtxInitCondConsistent:
    ∀ rs, ✓ rs → (Own rs ⊢ init_cond) →
    ∃ rs', ✓ rs' ∧ (Own rs' ⊢ init_cond ∗ CtxcbInitCond).

  (* Apply cancellation to linked spec module *)
  Lemma cancel_from_src:
    refines (mod_cancel, init_cond ∗ CtxcbInitCond)%I 
            (mod_src, init_cond ∗ CtxcbInitCond)%I.
  Proof.
    eapply Cancel.cancellation; et.
     (* try by econs.
    i. iIntros "%POST". iPureIntro. des; eauto. *)
  Qed.

  Lemma lib_sp_incl: sp_incl CtxcbAS.sp sp.
  Proof.
    i. rewrite /CtxcbAS.sp. unseal CRIS. econs; first prove_nodup.
    destruct fooInCtx. des. intros ? ?.
    rewrite /sp /ElimRel.sp_from /smod_src /to_sp alist_find_map /o_map //=.
    rewrite /sumbool_to_bool /or_else //=.
    des_ifs; ii; rewrite H in Heq1; clarify.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond ∗ CtxcbInitCond)%I (mod_tgt, CtxcbInitCond).
  Proof.
    eapply ctxr_refines.
    rewrite /init_cond /mod_src /smod_src /mod_tgt /Ctxcb.
    rewrite !add_interp_comm.
    
    (* consider identical modules in src/tgt as context (CtxcbA, CtxcbA) *)
    ctxr_norm.
    rewrite<- !hmod_add_assoc.
    apply ctxr_frameR.
    
    (* solve by transitivity:
      MaincbI ★ CelliocbI ⊆ MaincbI ★ CelliocbA ⊆ MaincbA ★ CelliocbA 
    *)
    etrans; cycle 1.
    { (* CelliocbI ⊆ctx CelliocbA *)
      ctxr_drop.
      eapply main_adequacy, CelliocbIA.sim.
    }

    etrans; cycle 1.
    { (* MaincbI ★ CelliocbA ⊆ctx MaincbA *)
      ctxr_norm.
      eapply main_adequacy, MaincbIA.sim.
      eapply lib_sp_incl.
    }

    rewrite /MaincbIAproof.MaincbIA.MaincbA /MaincbA.t. unseal CRIS.
    ctxr_refl.
  (*SLOW*)Qed.

  Lemma cancel_from_tgt :
    refines (mod_cancel, (init_cond ∗ CtxcbInitCond)%I)
            (mod_tgt, CtxcbInitCond).
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
      - rewrite /init_cond /MaincbA.InitCond /CelliocbA.InitCond.
        simplify_res.
        { iDestruct "H12" as "[H2 H3]".
          rewrite /CelliocbA.auth /CelliocbA.cell. iFrame. }
        all: solve_res.
    }
    des. eapply CtxInitCondConsistent in H1; et. des.

    destruct (H rs'); et.
    { des. et. }
  (*SLOW*)Qed.
End CelliocbAll. End CelliocbAll.
(* Print Assumptions CelliocbAll.behavioral_refinement. *)
