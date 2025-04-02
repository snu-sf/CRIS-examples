Require Import CRIS Cancel.
Require Import MemI MemA MemIAproof ImpPrelude.
Require Import IncrHeader IncrI IncrA IncrIAproof FAA_I FAA_A FAA_IAproof.
Require Import SchHeader SchI SchA SchIAproof SchTactics.

Module IncrAll.
  Import inv_instances.
  Local Definition u : univ_id := 1.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; IncrAΓ].
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].

  Definition IRΓ : Γ :=
    **[ir_invΓ u; ir_memΓ csl genv; SchAS.ir_SchAΓ; *[None]].
  Definition IRΣ : Σ :=
    **[ir_invΣ u; SchAS.ir_SchAΣ; IRΓ].

  Lemma IRΣ_valid : ✓ (IRΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply SchAS.ir_threadsRA_valid.
    - apply ir_memRA_valid.
    - apply SchAS.ir_tidRA_valid.
  Qed.

  (* source module *)
  Local Definition sp_user_s : string → option fspec :=
    to_sp (IncrAS.sp u ++ MemA.sp).
  Local Definition smod_src : SMod.t :=
    (IncrA.Mod u) ☆ (MemA.Mod) ☆ (SchA.Mod u sp_user_s ☆ SchA_link.Mod u).
  Local Definition sp_s : string → option fspec := sp_from smod_src.

  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod sp_s smod_src.
  Local Definition mod_tgt : HMod.t := (IncrI.t ★ FaaI.t) ★ (MemI.t csl genv) ★ (SchI.t).

  Local Definition SchInSp : sp_incl (SchAS.sp u sp_user_s) sp_s.
  Proof.
    ii; rewrite /sp_s /SchAS.sp /MemA.sp /IncrAS.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MainInSp : sp_incl (IncrAS.sp u) sp_user_s.
  Proof.
    ii; rewrite /sp_s /SchAS.sp /MemA.sp /IncrAS.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MemInSp : sp_incl MemA.sp sp_s.
  Proof.
    ii; rewrite /sp_s /SchAS.sp /MemA.sp /IncrAS.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.

  Local Definition init_cond : iProp Σ := MemA.init_cond csl genv ∗ SchA.init_cond.
  Local Definition main_fsp : fspec := IncrAS.main_spec u.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (smod_cancel, (init_cond ∗ main_fsp.(precond) (0, tt) tt↑ tt↑)%I) 
            (mod_src, init_cond).
  Proof. i; eapply cancellation; try by econs. i. iIntros "[_ [_ %POST]]". iPureIntro. des; eauto. Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    hexploit (IncrIA.ctxr u 0 sp_s (to_sp (SchAS.sp 0 (to_sp []))) sp_user_s sp_s).
    all: eauto using SchInSp, MainInSp, MemInSp.
    { rewrite /SchAS.sp; unseal CRIS. split; ii; ss. prove_nodup. }
    i; eapply ctxr_refines.
    rewrite -[(mod_src, _)]hmod_addc_empty_l.
    rewrite -[(mod_tgt, _)]hmod_addc_empty_r.
    rewrite /mod_src /mod_tgt ?add_interp_comm /init_cond.
    rewrite -?hmod_add_assoc. rewrite hmod_add_assoc.
    rewrite assoc. eapply ctxr_compose_hor.
    { etrans.
      { eapply ctxr_cond_frameR.
        replace (SMod.to_hmod _ (IncrA.Mod u)) with (IncrA.t u sp_s); cycle 1.
        { rewrite /IncrA.t; unseal CRIS; ss. }
        replace (SMod.to_hmod _ MemA.Mod) with (MemA.t u sp_s); cycle 1.
        { rewrite /MemA.t; unseal CRIS; ss. }
        eauto.
      }
      { rewrite ?hmod_add_assoc. eapply ctxr_frameL.
        etrans.
        { eapply ctxr_cond_frameR. eapply main_adequacy, FaaIA.sim. instantiate (1:=to_sp []).
          rewrite /SchAS.sp; unseal CRIS. split; ii; ss. prove_nodup.
        }
        etrans.
        { eapply ctxr_cond_frameL, ctxr_frameL, MemIA.ctxr. eauto using MemInSp. }
        { eapply ctxr_cond_strengthen; eauto. }
      }
    }
    eapply main_adequacy.
    replace (SMod.to_hmod _ (SchA.Mod u sp_user_s)) with (SchA.t u sp_s sp_user_s); cycle 1.
    { rewrite /SchA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod _ (SchA_link.Mod _)) with (SchA_link.t u sp_s); cycle 1.
    { unfold_hmod; ss. }
    eapply SchIA.sim; eauto using SchInSp.
    { rewrite /sp_sub /sp_user_s /sp_s /IncrAS.sp /MemA.sp; unseal CRIS. ii; ss.
      des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }
  Qed.

  Lemma cancel_tgt :
    refines (smod_cancel, (init_cond ∗ main_fsp.(precond) (0, tt) tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel (IRΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    hexploit H.
    { rewrite /mod_tgt /IncrI.t /MemI.t /SchI.t /FaaI.t; unseal CRIS; prove_nodup. }
    clear H; intros [WF H].
    destruct (H (IRΣ ⋅ initial_resource_own_admin)).
    { apply IRΣ_valid. }
    { clear H. simplify_res.
      {
        iAssert (SchAS.tid_admin None) with "[H18]" as "TID".
        { rewrite /SchAS.tid_admin. unseal "SchA". eauto. }
        iPoseProof (SchAS.tid_admin_none_split 0 with "TID") as "[TA TU]".
        iSplitR "U W H1 TU".
        - rewrite /init_cond. iSplitL "H20".
          { iAssert (mem_init csl genv) with "[H20]" as "[$ _]". eauto. }
          iSplitL "H26".
          { rewrite /SchAS.init_threads. unseal "SchA". eauto. }
          eauto.
        - iPoseProof (make_own_admin with "H1") as "$".
          unfold_pre_post; iFrame. eauto.
      }
      all: solve_res.
    }
    { exists x; des; eauto. }
  Qed.
End IncrAll.
