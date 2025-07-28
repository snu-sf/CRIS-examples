Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonMainI.
Require Import CannonA CannonMainA.
Require Import CannonIAproof CannonMainIAproof.

Module CannonAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; cannonΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Local Definition irΓ : Γ := **[ir_invΓ; CannonAS.irΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ].

  Local Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply CannonAS.ir_valid.
  Qed.

  Local Definition smod_src : SMod.t := CannonA.smod ☆ (MainA.smod 1).
  Local Definition mod_top : Mod.t := (SMod.to_mod sp_none (SMod.cancel smod_src)).
  Local Definition mod_tgt : Mod.t := CannonI.t ★ (MainI.t 1).
  
  Local Definition sp : sp_type := sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition init_cond : iProp Σ :=
    winv (⊤, ⊤) ∗ CannonA.init_cond ∗ MainA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_top, init_cond)
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    - ii; des; subst; inv FIND; ss; rewrite !eq_rel_dec_correct in H0; des_ifs.
    - econs; [refl|]; i; inv NS; des; inv H; des; inv H1;
      rewrite !eq_rel_dec_correct in H2; des_ifs.
    - econs; unfold_mod; ss; prove_nodup.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src add_interp_comm.

    etrans; cycle 1.
    { ctxr_rotate. ctxr_drop. eapply CannonIA.ctxr. }

    etrans; cycle 1.
    { ctxr_rotate. ctxr_drop. eapply CannonMainIA.ctxr.
      instantiate (1:=sp).
      rewrite /CannonAS.Sp. unseal CRIS. econs; first prove_nodup.
      ii. inv H. des_ifs.
      unfold dec, option_Dec, AList.option_Dec_obligation_1 in Heq.
      des_ifs.
    }

    rewrite /CannonA.t /MainA.t /init_cond. unseal CRIS. 
    eapply ctxr_cond_strengthen.
    iIntros "[? [? ?]]". iFrame.
  (*SLOW*)Admitted.

  Lemma top_tgt :
    refines (mod_top, init_cond)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf:
    Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt /CannonI.t /MainI.t; unseal CRIS; prove_nodup.
  Qed.

  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin; iFrame.
        iDestruct "H12" as "[? ?]". iFrame. et.
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
    rewrite IV0 /init_cond {1}winv_split_empty. iIntros ">[[? ?] ?]". iFrame. et.
  Qed.
(*SLOW*)End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)
