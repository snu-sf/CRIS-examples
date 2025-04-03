Require Import CRIS Cancel.

Require Import MutHeader MutMainHeader MutFA MutGA MutMainA.
Require Import MutFI MutGI MutMainI.
Require Import MutFIAproof MutGIAproof MutMainIAproof.
Require Import APCHeader APC APCI APCA APCC.
Require Import APCIAproof APCACproof.

Module MutAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Definition irΓ : Γ := **[ir_invΓ 0].
  Definition irΣ : Σ := **[irΓ; ir_invΣ 0].

  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof. solve_ir_valid. Qed.

  Local Definition smod_src : SMod.t := MutMainA.Mod ☆ MutFA.Mod ☆ MutGA.Mod ☆ APCC.Mod.
  Local Definition sp : string → option fspec := sp_from smod_src.

  Local Definition smod_pure : SMod.t := MutFA.Mod ☆ MutGA.Mod.
  Local Definition sp_pure : string → option fspec := sp_from smod_pure.

  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := MutMainI.t ★ MutFI.t ★ MutGI.t ★ APCI.t.

  Local Definition main_fsp : fspec := MutMainA.main_spec.
  Local Definition init_cond : iProp Σ := MutFA.init_cond ∗ MutGA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            ((mod_src, init_cond) : HMod.modc).
  Proof. eapply cancellation; try by econs. i. iIntros "%POST". iPureIntro. des; eauto. Qed.

  Ltac prove_sp :=
    rewrite /APCA.Sp /MutFA.SpF /MutGA.SpG /sp /smod_src /sp_pure /sp_incl /sp_sub /find_body
      /pure_specbody /sp_from /smod_pure /option_map; try unseal CRIS; try prove_nodup;
    ii; ss; rewrite ->!eq_rel_dec_correct in *; des_ifs; eexists; ss.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    unfold mod_src, mod_tgt. rewrite !add_interp_comm.
    do 2 rewrite -hmod_add_assoc.
    etrans. { eapply ctxr_comm. }
    etrans.
    { rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR.
      replace (SMod.to_hmod sp APCC.Mod) with (APCC.t sp); cycle 1.
      { unfold APCC.t. unseal CRIS. ss. }
      eapply APCAC.ctxr.
      { instantiate (1:=sp). prove_sp. }
      { instantiate (1:=sp_pure). prove_sp. } 
      { prove_sp. }
    }
    etrans. { eapply ctxr_comm. }
    rewrite !hmod_add_assoc. rewrite -(hmod_add_assoc (SMod.to_hmod sp MutFA.Mod)).
    etrans.
    { eapply ctxr_compose_mix.
      { replace (SMod.to_hmod sp MutMainA.Mod) with (MutMainA.t sp); cycle 1.
        { unfold MutMainA.t. unseal CRIS. ss. }
        eapply MutMainIA.ctxr; prove_sp.
      }
      { replace (SMod.to_hmod sp MutFA.Mod) with (MutFA.t sp); cycle 1.
        { unfold MutFA.t. unseal CRIS. ss. }
        replace (SMod.to_hmod sp MutGA.Mod) with (MutGA.t sp); cycle 1.
        { unfold MutGA.t. unseal CRIS. ss. }
        rewrite !hmod_add_assoc.
        etrans.
        { eapply ctxr_compose_mix.
          { eapply MutFIA.ctxr; prove_sp. }
          { eapply MutGIA.ctxr; prove_sp. }
        }
        rewrite hmod_addc_empty_l -hmod_add_assoc. refl.
      }
    }
    rewrite hmod_addc_empty_l -!hmod_add_assoc.
    eapply ctxr_frameL.
    eapply APCIA.ctxr.
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
    hexploit H.
    { rewrite /mod_tgt /MutMainI.t /MutFI.t /MutGI.t /APCI.t; unseal CRIS; prove_nodup. }
    clear H; intros [_ H].
    destruct (H (irΣ ⋅ initial_resource_own_admin)).
    { apply irΣ_valid. }
    { clear H. simplify_res.
      { eauto. }
      all: solve_res.
    }
    { exists x; des; eauto. }
  (*FAST*)Qed.
End MutAll.
(* Print Assumptions MutAll.behavioral_refinement. *)
