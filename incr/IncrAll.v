Require Import CRIS Cancel.
Require Import MemI MemA MemIAproof ImpPrelude.
From CRIS.incr Require Import Header ClientI ClientA ClientIA FaaI FaaA FaaIA.
Require Import SchHeader SchI SchA SchIAproof SchTactics.

Module ClientAll.
  Import inv_instances.
  (* Local Definition u : univ_id := 1. *)

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; memΓ; schΓ; incrΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; schΣ].

  Definition IRΓ : Γ :=
    **[ir_invΓ; ir_memΓ csl genv; SchAS.ir_schΓ; *[None]].
  Definition IRΣ : Σ :=
    **[IRΓ; ir_invΣ; SchAS.ir_schΣ].

  Lemma IRΣ_valid : ✓ (IRΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_memRA_valid.
    - apply SchAS.ir_tidRA_valid.
    - apply SchAS.ir_threadsRA_valid.
  Qed.

  (* source module *)
  Local Definition sp_user_s : string → option fspec :=
    to_sp (ClientA.sp ⊤ ++ MemA.sp).
  Local Definition smod_src : SMod.t :=
    (ClientA.Mod ⊤) ☆ (MemA.Mod) ☆ (SchA.Mod ⊤ sp_user_s ☆ SchAPure.Mod ⊤).
  Local Definition sp_s : string → option fspec := sp_from smod_src.

  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod sp_s smod_src.
  Local Definition mod_tgt : HMod.t := ClientI.t ★ FaaI.t ★ (MemI.t csl genv) ★ (SchI.t).

  Local Definition SchInSp0: sp_incl (SchAS.sp ⊤ (to_sp [])) (to_sp (SchAS.sp ⊤ (to_sp []))).
  Proof.
    split; [|refl]. rewrite /SchAS.sp; unseal CRIS. prove_nodup.
  Qed.
  Local Definition SchInSp : sp_incl (SchAS.sp ⊤ sp_user_s) sp_s.
  Proof.
    ii; rewrite /sp_s /SchAS.sp /MemA.sp /ClientA.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MainInSp : sp_incl (ClientA.sp ⊤) sp_user_s.
  Proof.
    ii; rewrite /sp_s /SchAS.sp /MemA.sp /ClientA.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Local Definition MemInSp : sp_incl MemA.sp sp_s.
  Proof.
    ii; rewrite /sp_s /SchAS.sp /MemA.sp /ClientA.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.

  Local Definition init_cond : iProp Σ := MemA.init_cond csl genv ∗ SchA.init_cond.
  Local Definition main_fsp : fspec := ClientA.main_spec ⊤.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (smod_cancel, (init_cond ∗ main_fsp.(precond) (0, tt) tt↑ tt↑)%I) 
            (mod_src, init_cond).
  Proof. i; eapply cancellation; try by econs. i. iIntros "[_ [_ %POST]]". iPureIntro. des; eauto. Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src !add_interp_comm.

    (* abstraction of Sch *)
    etrans; cycle 1.
    { do 3 ctxr_drop.
      eapply main_adequacy, SchIA.sim.
      - apply SchInSp.
      - rewrite /sp_sub /sp_user_s /sp_s /ClientA.sp /MemA.sp; unseal CRIS.
        ii; ss. des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 3 ctxr_drop.
      eapply MemIA.ctxr.
    }

    (* abstraction of Faa *)
    etrans; cycle 1.
    { do 2 ctxr_drop.
      eapply main_adequacy, FaaIA.sim.
      (* apply SchInSp0. *)
    }
    rewrite /FaaIA.FaaIA.MA.
    
    (* abstraction of Incr *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply ClientIA.ctxr.
      - instantiate (1:=⊤). set_solver.
      - apply MainInSp.
      - apply SchInSp.
      (* - apply SchInSp0.
      - apply MemInSp.
      - unfold u. nia. *)
    }

    etrans; cycle 1.
    { ctxr_rotate. ctxr_refl. }
    
    rewrite /SchIAproof.SchIA.SchAMod.
    rewrite /SchIAproof.SchIA.SchA /SchIAproof.SchIA.SchAPure.
    rewrite /SchA.t /SchAPure.t /ClientA.t /MemA.t.
    unseal CRIS.
    
    eapply ctxr_cond_strengthen.
    { iIntros "[? ?]". iFrame. }
  (*SLOW*)Qed.

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
    { rewrite /mod_tgt /ClientI.t /MemI.t /SchI.t /FaaI.t; unseal CRIS; prove_nodup. }
    clear H; intros [WF H].
    destruct (H (IRΣ ⋅ initial_resource_own_admin)).
    { apply IRΣ_valid. }
    { clear H. simplify_res.
      { iAssert (SchAS.tid_admin None) with "[H22]" as "TID".
        { rewrite /SchAS.tid_admin. unseal "SchA". eauto. }
        iPoseProof (SchAS.tid_admin_none_split 0 with "TID") as "[TA TU]".
        iSplitR "H1 TU U W".
        - rewrite /init_cond. iSplitL "H24".
          { iAssert (mem_init csl genv) with "[H24]" as "[$ _]". eauto. }
          iSplitL "H8".
          { rewrite /SchAS.init_threads. unseal "SchA". eauto. }
          eauto.
        - iPoseProof (make_own_admin with "H1") as "$".
          unfold_pre_post; iFrame. done.
      }
      all: solve_res.
    }
    { exists x; des; eauto. }
  (*SLOW*)Qed.
End ClientAll.
