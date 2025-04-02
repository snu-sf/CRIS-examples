Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonMainI.
Require Import CannonA CannonMainA.
Require Import CannonIAproof CannonMainIAproof.

Module CannonAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; cannonΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Local Definition irΓ : Γ := **[ir_invΓ 1; CannonAS.irΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ 1].

  Local Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply CannonAS.ir_valid.
  Qed.

  Local Definition smod_src : SMod.t := CannonA.Mod ☆ (MainA.Mod 1).
  Local Definition sp : string → option fspec := sp_from smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := CannonI.t ★ (MainI.t 1).

  Local Definition main_fsp : fspec := MainAS.main_spec.
  Local Definition init_cond : iProp Σ := CannonA.init_cond ∗ MainA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I) 
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines. 
    rewrite -[(mod_tgt, _)]hmod_addc_empty_r.
    unfold mod_src, mod_tgt. rewrite add_interp_comm.
    eapply ctxr_compose_hor.
    { replace (SMod.to_hmod _ CannonA.Mod) with (CannonA.t sp); cycle 1.
      { unfold CannonA.t. unseal CRIS. ss. }
      eapply CannonIA.ctxr.
    }
    { replace (SMod.to_hmod _ (MainA.Mod 1)) with (MainA.t 1 sp); cycle 1.
      { unfold MainA.t. unseal CRIS. ss. }
      eapply CannonMainIA.ctxr.
      i. rewrite /CannonAS.Sp. unseal CRIS. econs; first prove_nodup.
      ii; rewrite -FIND /sp /sp_from /smod_src //=; des_ifs; ss; des_ifs.
    }
  Qed.

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
    hexploit H.
    { rewrite /mod_tgt /CannonI.t /MainI.t; unseal CRIS; prove_nodup. }
    clear H; intros [WF H].
    destruct (H (irΣ ⋅ initial_resource_own_admin)).
    { apply irΣ_valid. }
    { clear H. simplify_res.
      {
        iPoseProof (CannonAS.ReadyBall with "[H12]") as "[R B]"; eauto.
        iSplitL "R".
        { iFrame. }
        unfold_pre_post. iFrame. eauto.
      }
      all: solve_res.
    }
    { exists x; des; eauto. }
  Qed.
End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)
