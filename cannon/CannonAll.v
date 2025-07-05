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

  Local Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply CannonAS.ir_valid.
  Qed.

  Local Definition smod_src : SMod.t := CannonA.Mod ☆ (MainA.Mod 1).
  Local Definition sp : sp_type := ElimRel.sp_from smod_src.
  Local Definition mod_cancel : HMod.t := (SMod.to_hmod sp_none (SMod.cancel smod_src)).
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := CannonI.t ★ (MainI.t 1).

  Local Definition init_cond : iProp Σ := CannonA.init_cond ∗ MainA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, init_cond)
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply Cancel.cancellation.
    - ii; des; subst; inv FIND; ss; rewrite !eq_rel_dec_correct in H0; des_ifs.
    - econs; [refl|]; i; inv NS; des; inv H; des; inv H1;
      rewrite !eq_rel_dec_correct in H2; des_ifs.
    - econs; unfold_hmod; ss; prove_nodup.
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
    iIntros "[? ?]". iFrame.
  (*SLOW*)Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, init_cond)
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
    hexploit H.
    { rewrite /mod_tgt /CannonI.t /MainI.t; unseal CRIS; prove_nodup. }
    clear H; intros [WF H].
    destruct (H (irΣ ⋅ initial_resource_own_admin)).
    { apply irΣ_valid. }
    { clear H. simplify_res.
      { iPoseProof (CannonAS.ReadyBall with "[H12]") as "[R B]"; eauto.
        iSplitL "R".
        { iFrame. }
        unfold_pre_post. iFrame.
      }
      all: solve_res.
    }
    { exists x; des; eauto. }
  Qed.
(*SLOW*)End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)
