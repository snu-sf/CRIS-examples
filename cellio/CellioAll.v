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
  Local Definition smod_src : SMod.t := MainA.Mod ☆ CtxA.

  Local Definition sp : string → option fspec := sp_from smod_src.
  Local Definition Ctx := Seal.sealing CRIS (SMod.to_hmod sp CtxA).
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := MainI.t ★ CellioI.t ★ Ctx.
  
  Local Definition main_fsp : fspec := fspec_trivial.
  Local Definition CtxInitCond : iProp Σ := emp%I.
  Local Definition init_cond : iProp Σ := MainA.InitCond ∗ CellioA.InitCond ∗ CtxInitCond.
  
  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I) 
            (mod_src, init_cond).
  Proof. eapply cancellation; try by econs. i. iIntros "%POST". iPureIntro. des; eauto. Qed.

  Local Definition trivial_specbody body := {|fsb_fspec := fspec_trivial; fsb_body := body|}.

  Hypothesis ModulesWF : HMod.wf mod_tgt.
  Hypothesis inputInCtx : ∃ sc input (SCP: incl sc CtxA.(SMod.scopes)),
    alist_find CtxHdr.input (SMod.fnsems CtxA) = Some (sc, trivial_specbody input).
  Hypothesis fooInCtx : ∃ sc foo (SCP: incl sc CtxA.(SMod.scopes)),
    alist_find CtxHdr.foo (SMod.fnsems CtxA) = Some (sc, trivial_specbody foo).

  Lemma lib_sp_incl: sp_incl CtxAS.sp sp.
  Proof.
    i. rewrite /CtxAS.sp. unseal CRIS. econs; first prove_nodup.
    destruct inputInCtx, fooInCtx. des.
    ii; rewrite -FIND /sp /sp_from /smod_src //=. des_ifs; ss; des_ifs.
    { rewrite eq_rel_dec_correct in Heq0. des_ifs.
      rewrite /option_map. des_ifs.
    }
    { rewrite eq_rel_dec_correct in Heq1. des_ifs.
      rewrite /option_map. des_ifs.
    }
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    (* consider identical modules in src/tgt as context (CtxA, CtxA) *)
    eapply ctxr_refines.
    rewrite -[(_, emp%I)]hmod_addc_empty_r /init_cond -!hmod_addc_assoc.
    rewrite /mod_src /mod_tgt !add_interp_comm -!hmod_add_assoc /Ctx.
    unseal CRIS. eapply ctxr_frameR, ctxr_cond_frameR.
    (* solve by transitivity:
      MainI ★ CellioI ⊆ MainI ★ CellioA ⊆ MainA ★ CellioA 
    *)
    etrans.
    {
      (* MainI ★ CellioA ⊆ MainA *)
      rewrite -[(SMod.to_hmod _ MainA.Mod)](Seal.sealing_eq CRIS).
      instantiate (1:= (MainI.t ★ (CellioA.t sp), (emp ∗ CellioA.InitCond)%I)).
      eapply ctxr_cond_frameR, main_adequacy.
      (* assert (XXX := @MainIA.sim). *)
      eapply MainIA.sim.
      eapply lib_sp_incl.
    }
    (* MainI ★ CellioI ⊆ MainI ★ CellioA 
      by CellioI ⊆ctx CellioA *)
    rewrite -[(_, emp%I)]hmod_addc_empty_r.
    eapply ctxr_frameL, ctxr_cond_frameL, main_adequacy, CellioIA.sim.
    eapply lib_sp_incl.
  (*FAST*)Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod mod_cancel (irΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit (H ModulesWF).
    clear H; intros [WF H]. 
    destruct (H (irΣ ⋅ initial_resource_own_admin)).
    { apply irΣ_valid. }
    { clear H. simplify_res.
      { iDestruct "H12" as "[H2 H3]".
        iSplitL "H2".
        { iFrame. done. }
        { eauto. }
      }
      all: solve_res.
    }
    { exists x; des; eauto. }
  (*FAST*)Qed.
End CellioAll. End CellioAll.
(* Print Assumptions CellioAll.behavioral_refinement. *)
