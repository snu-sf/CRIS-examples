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
    rewrite /mod_src /mod_tgt /smod_src add_interp_comm.

    etrans; cycle 1.
    { ctxr_rotate. ctxr_drop. eapply CannonIA.ctxr. }

    etrans; cycle 1.
    { ctxr_rotate. ctxr_drop. eapply CannonMainIA.ctxr.
      instantiate (1:=sp).
      rewrite /CannonAS.Sp. unseal CRIS. econs; first prove_nodup.
      ii; rewrite -FIND /sp /sp_from /smod_src //=; des_ifs; ss; des_ifs.
    }

    rewrite /CannonA.t /MainA.t /init_cond. unseal CRIS. 
    eapply ctxr_cond_strengthen.
    iIntros "[? ?]". et.
  (*SLOW*)Qed.

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
(*SLOW*)End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)
