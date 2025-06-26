Require Import CRIS.
From CRIS.spinlock Require Import Header LockI LockA LockIA MainI MainA MainIA.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SchHeader SchI SchA SchIAproof.
Require Import ElimRel SModCancel Cancellation.

(* Cancellation *)
Module MainAll.
  Import inv_instances.

  (* initialization parameters for memory module *)
  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  (* HRA & GRA *)
  Local Instance Γ : HRA := ##[invΓ; memΓ; schΓ; spinlockΓ; spinlockmainΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; schΣ].

  (* initial resources for HRA & GRA *)
  Definition irΓ : Γ :=
    **[ir_invΓ; ir_memΓ csl genv; SchAS.ir_schΓ; LockAS.ir; MainAS.ir].
  Definition irΣ : Σ :=
    **[irΓ; ir_invΣ; SchAS.ir_schΣ].

  (* validity lemma for the initial resource irΣ *)
  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_memRA_valid.
    - apply SchAS.ir_tidRA_valid.
    - apply SchAS.ir_threadsRA_valid.
  Qed.

  (* the target module *)
  Local Definition mod_tgt : HMod.t := SpinLockMainI.t ★ MemI.t csl genv ★ SchI.t ★ SpinLockI.t.

  (* sp of source module (scheduler spec excluded) *)
  Local Definition sp_user_s : string → option fspec :=
    to_sp (MainAS.sp ⊤ ++ LockAS.sp ⊤).

  (* the source SMod *)
  Local Definition smod_src : SMod.t :=
    SpinLockMainA.Mod ⊤ ☆ SpinLockA.Mod ⊤ ☆ (SchA.Mod ⊤ sp_user_s ☆ SchAPure.Mod ⊤).
  (* the source sp *)
  Local Definition sp_s : string → option fspec :=
    sp_from smod_src.
  (* the source HMod *)
  Local Definition mod_src : HMod.t := SMod.to_hmod sp_s smod_src.

  (* initial condition for the source *)
  Local Definition init_cond : iProp Σ := (MemP.init_cond csl genv ∗ SchA.init_cond)%I.

  (* source module after cancellation *)
  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.

  (* Some assumptions on sp inclusion *)
  Lemma SchInSp : sp_incl (SchAS.sp ⊤ sp_user_s) sp_s.
  Proof.
    rewrite /sp_user_s /SchAS.sp /sp_s /smod_src; unseal CRIS. split; first prove_nodup.
    ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Lemma MainInSp : sp_incl (MainAS.sp ⊤) sp_user_s.
  Proof.
    rewrite /sp_user_s /MainAS.sp /sp_s /smod_src; unseal CRIS. split; first prove_nodup.
    ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.
  Lemma UserInSp : sp_sub sp_user_s sp_s.
  Proof.
    rewrite /sp_user_s /sp_s ; unseal CRIS.
    ii; ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed.

  (* Refinement between smod_cancel and smod_src *)
  Local Definition main_fsp : fspec := MainAS.main_spec ⊤.
  Lemma cancel_src :
    refines (smod_cancel, init_cond ∗ main_fsp.(precond) (0, tt) tt↑ tt↑)%I
            (mod_src,     init_cond).
  Proof. eapply cancellation; try by econs. i. unfold_pre_post. iIntros "[_ [_ [-> ->]]]". done. Qed.

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    apply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt /init_cond !add_interp_comm.

    (* abstraction of Sch *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 3 ctxr_drop.
      eapply SchIA.ctxr.
      - apply SchInSp.
      - rewrite /sp_sub /sp_user_s /sp_s /MainAS.sp; unseal CRIS.
        ii; ss. des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 4 ctxr_drop.
      eapply MemIP.ctxr.
    }

    (* abstraction of SpinLock *)
    etrans; cycle 1.
    { do 2 ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply LockIA.ctxr.
      { instantiate (1:=⊤). set_solver. }
      apply SchInSp.
    }
    
    (* abstraction of SpinLockMain *)
    etrans; cycle 1.
    { do 2 ctxr_drop. ctxr_swap. ctxr_rotate.
      eapply MainIA.ctxr.
      - apply SchInSp.
      - apply MainInSp.
    }

    (* elimination of MemP *)
    etrans; cycle 1.
    { do 4 ctxr_rotate. do 4 ctxr_drop. eapply CFilter.elim_module. }
    rewrite hmod_add_empty_r.
    
    etrans; cycle 1.
    { do 3 ctxr_rotate.
      ctxr_refl. }
    
    rewrite /SchIAproof.SchIA.SchAMod.
    rewrite /SchIAproof.SchIA.SchA /SchIAproof.SchIA.SchAPure.
    rewrite /SchA.t /SchAPure.t /SpinLockA.t /SpinLockMainA.t.
    unseal CRIS.
    
    eapply ctxr_cond_strengthen.
    { iIntros "[? ?]". iFrame. }
  (*SLOW*)Qed.

  (* source HMod ⊆ source SMod ⊆ cancelled HMod *)
  Lemma cancel_tgt :
    refines (smod_cancel, (init_cond ∗ (main_fsp).(precond) (0, tt) tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  (* tgt HMod ⊆ cancelled HMod *)
  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel (irΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    hexploit H.
    { rewrite /mod_tgt /SpinLockMainI.t /MemI.t /SchI.t /SpinLockI.t; unseal CRIS; prove_nodup. }
    clear H; intros [WF H].
    destruct (H ((irΣ ⋅ initial_resource_own_admin))).
    { apply irΣ_valid. }
    (* initial condition constructions - wrap them by simplify_res and solve_res *)
    { clear H. simplify_res.
      { iAssert (SchAS.tid_admin None) with "[H26]" as "TID".
        { rewrite /SchAS.tid_admin. unseal "SchA". iFrame. }
        iPoseProof (SchAS.tid_admin_none_split 0 with "TID") as "[TID1 TID2]".
        { iSplitR "H1 U W TID2"; cycle 1.
          { iPoseProof (make_own_admin with "H1") as "$".
            unfold_pre_post; iFrame. done.
          }
          rewrite /init_cond. iSplitL "H28".
          { iAssert (mem_init csl genv) with "[H28]" as "[$ _]". eauto. }
          iSplitL "H8".
          { rewrite /SchAS.init_threads. unseal "SchA". eauto. }
          { iFrame. }
        }
      }
      all: solve_res.
    }
    { exists x; des; eauto. }
  (*SLOW*)Qed.
End MainAll.
