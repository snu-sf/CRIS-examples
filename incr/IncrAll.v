Require Import CRIS Cancel.
Require Import MemI MemA MemIAproof ImpPrelude.
Require Import SchHeader SchI SchA SchIAproof SchTactics.
From CRIS.incr Require Import Header ClientI ClientA ClientIA FaaI FaaA FaaIA.

Section TMP.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.
  Lemma tid_admin_none :
    own base_γ SchAS.ir_tidRA ⊢ SchAS.tid_admin None.
  Proof using.
    rewrite /SchAS.tid_admin. unseal "SchA". et.
  Qed.
  Lemma tid_admin_some tid :
    own base_γ (SchAS.tid_admin_r (Some tid), None) ⊢ SchAS.tid_admin (Some tid).
  Proof using.
    rewrite /SchAS.tid_admin. unseal "SchA". et.
  Qed.
  
End TMP.

Module ClientAll.
  Import inv_instances.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; memΓ; schΓ; incrΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; schΣ].

  Definition irΓ : Γ :=
    **[ir_invΓ; ir_memΓ csl genv; SchAS.ir_schΓ; *[None]].
  Definition irΣ : Σ :=
    **[irΓ; ir_invΣ; SchAS.ir_schΣ].

  Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_memRA_valid.
    - apply SchAS.ir_tidRA_valid.
    - apply SchAS.ir_threadsRA_valid.
  Qed.

  (* source module *)
  Local Definition sp_user_s : spl_type :=
    ClientA.sp ⊤ 1%Qp.
  Local Definition smod_src : SMod.t :=
    (ClientA.smod ⊤ 1%Qp) ☆ (SchA.smod sp_user_s).
  Local Definition mod_top : Mod.t := SMod.to_mod sp_none (SMod.cancel smod_src).
  Local Definition mod_tgt : Mod.t := ClientI.t ★ FaaI.t ★ (MemI.t csl genv) ★ (SchI.t).

  Local Definition sp : string → option fspec := sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  (* Local Definition SchInSp0: sp_incl (SchAS.sp ⊤ (to_sp [])) (to_sp (SchAS.sp ⊤ (to_sp []))).
  Proof.
    split; [|refl]. rewrite /SchAS.sp; unseal CRIS. prove_nodup.
  Qed. *)
  Local Definition SchInSp : sp_incl (SchAS.sp sp_user_s ⊤ 1%Qp) sp.
  Proof.
    rewrite /SchAS.sp; unseal CRIS.
    split; [prove_nodup|].
    intros ??; ss; des_ifs; des_sumbool; clarify; intros INV; inv INV;
      rewrite /sp /smod_src /sp_from /= /to_sp /=; des_ifs; ss.
  Qed.
  Local Definition UserInSp : sp_incl sp_user_s sp.
  Proof.
    rewrite /sp_user_s /ClientA.sp /MemA.sp; unseal CRIS.
    split; [prove_nodup|].
    intros ??; ss; des_ifs; des_sumbool; clarify; intros INV; inv INV;
      rewrite /sp /smod_src /sp_from /= /to_sp /=; des_ifs; ss.
  Qed.
  Local Definition MainInSp : spl_sub (ClientA.sp ⊤ 1%Qp) sp_user_s.
  Proof.
    rewrite /spl_sub /sp_user_s /ClientA.sp /ClientA.incr_spec /=.
    ii; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  (* Local Definition MemInSp : sp_incl MemA.sp sp.
  Proof.
    ii; rewrite /sp /SchAS.sp /MemA.sp /ClientA.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed. *)

  Local Definition init_cond : iProp Σ :=
    MemA.init_cond csl genv ∗ SchA.init_cond ∗ ClientIA.ClientIA.init_cond ⊤ 1%Qp.
  (* Local Definition main_fsp : fspec := ClientA.main_spec ⊤ 1%Qp. *)

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_top, init_cond) (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { ii; des; subst; inv FIND; ss.
      rewrite !eq_rel_dec_correct in H0; des_ifs.
    }
    { econs; [refl|]; i; inv NS; des; inv H; des; inv H1;
      rewrite !eq_rel_dec_correct in H2; des_ifs.
    }
    { econs; unfold_mod; ss; prove_nodup. }
  Qed.

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
      - apply UserInSp.
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
    }
    rewrite /FaaIA.FaaIA.MA.
    
    (* abstraction of Incr *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply ClientIA.ctxr.
      - instantiate (1:=⊤). set_solver.
      - apply MainInSp.
      - apply SchInSp.
    }

    etrans; cycle 1.
    { ctxr_rotate. ctxr_refl. }

    (* elimination of mem *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 2 ctxr_drop. eapply CFilter.elim_module. }
    rewrite -mod_add_empty_r.

    rewrite /SchIAproof.SchIA.SchAMod.
    rewrite /SchA.t /ClientA.t /MemA.t.
    unseal CRIS.
    ctxr_rotate.
    
    eapply ctxr_cond_strengthen.
    { iIntros "[? [? ?]]". iFrame. }
  (*SLOW*)Qed.

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
    rewrite /mod_tgt /ClientI.t /FaaI.t /MemI.t /SchI.t; unseal CRIS; prove_nodup.
  Qed.

  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin; iFrame.
        erewrite (*SchAS.*)tid_admin_none.
        iMod (SchAS.tid_admin_none_split 0 with "H22") as "[TA TU]".
        iSplitR "TA TU".
        - rewrite /init_cond. iAssert (mem_init csl genv) with "[H24]" as "[$ _]". eauto. done.
        - unfold_pre_post; iFrame. done.
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
    rewrite IV0 /init_cond /ClientIA.ClientIA.init_cond /ClientA.init_cond.
    rewrite {1}winv_split_empty. iIntros ">[? [? [[? ?] ?]]]". iFrame. et.
  (*SLOW*)Qed.
End ClientAll.
