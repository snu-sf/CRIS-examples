(* Require Import CRIS.
From CRIS.spinlock_pa Require Import Header LockI LockA LockIA MainI MainA MainIA.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SchHeader SchI SchA SchIAproof.
Require Import Cancel.

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
  Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_memRA_valid.
    - apply SchAS.ir_tidRA_valid.
    - apply SchAS.ir_threadsRA_valid.
  Qed.

  (* sp of source module (scheduler spec excluded) *)
  Local Definition sp_user : spl_type :=
    MainAS.sp ⊤ 1.

  (* the source SMod *)
  Local Definition smod_src : SMod.t :=
    SpinLockMainA.smod ⊤ 1 ☆ SchA.smod sp_user 1.
  (* the top-level module after cancellation *)
  Local Definition mod_top : Mod.t := SMod.to_mod sp_none (SMod.cancel smod_src).
  (* the target module *)
  Local Definition mod_tgt : Mod.t := SpinLockMainI.t ★ SpinLockI.t ★ MemI.t csl genv ★ SchI.t .

  (* the source sp *)
  Local Definition sp : sp_type := sp_from smod_src.
  (* the source Mod *)
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  (* initial condition for the source *)
  Local Definition init_cond : iProp Σ :=
    (MainAS.init_cond ⊤ 1 ∗ MemP.init_cond csl genv ∗ SchA.init_cond)%I.

  (* Some assumptions on sp inclusion *)
  Lemma SchInSp : sp_incl (SchAS.sp sp_user ⊤ 1) sp.
  Proof.
    rewrite /sp /SchAS.sp /sp_from /to_sp. unseal CRIS.
    split; first prove_nodup.
    ii; s in H. by repeat (destruct (dec _ _); s in H; [depdes e; depdes H; et|]).
  Qed.

  Lemma MainInSp : spl_sub (MainAS.sp ⊤ 1) sp_user.
  Proof.
    rewrite /sp_user /MainAS.sp /sp_from /to_sp.
    ii. s in H. des_ifs.
  Qed.

  Lemma UserInSp : sp_incl sp_user sp.
  Proof.
    rewrite /sp_user /MainAS.sp /sp /sp_from /to_sp.
    split; first prove_nodup.
    ii; s in H. by repeat (destruct (dec _ _); s in H; [depdes e; depdes H; et|]).
  Qed.

  (* Refinement between smod_cancel and smod_src *)
  (* Local Definition main_fsp : fspec := MainAS.main_spec ⊤ 1. *)
  
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

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    apply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt /init_cond !add_interp_comm.

    (* abstraction of Sch *)
    etrans; cycle 1.
    { do 3 ctxr_drop.
      eapply SchIA.ctxr.
      - apply SchInSp.
      - apply UserInSp.
    }

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 3 ctxr_drop.
      eapply MemIP.ctxr.
    }

    (* abstraction of SpinLock *)
    etrans; cycle 1.
    { do 2 ctxr_drop.
      eapply (LockIA.ctxr ⊤); cycle 1.
      set_solver.
    }
    
    (* abstraction of SpinLockMain *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply MainIA.ctxr.
      - set_solver.
      - apply SchInSp.
      - apply MainInSp.
    }

    (* elimination of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_drop. eapply CFilter.elim_module. }
    rewrite -mod_add_empty_r.

    (* elimination of SpinLock *)
    etrans; cycle 1.
    { do 2 ctxr_drop. eapply CFilter.elim_module. }
    rewrite -mod_add_empty_r.

    etrans; cycle 1.
    { ctxr_rotate. refl. }

    rewrite /SpinLockMainA.t /SchA.t. unseal CRIS.
    eapply ctxr_cond_strengthen; et.
  (*SLOW*)Qed.

  (* source Mod ⊆ source SMod ⊆ cancelled Mod *)
  Lemma cancel_tgt :
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
    rewrite /mod_tgt /SpinLockMainI.t /SpinLockI.t /MemI.t /SchI.t; unseal CRIS.
    prove_nodup.
  Qed.
  
  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { erewrite make_own_admin; iFrame.
        erewrite SchAS.make_tid_admin, SchAS.tid_admin_none_split.
        iMod "H26" as "[? ?]". iDestruct "H28" as "[? ?]".
        iFrame; et.
      }
      all: solve_res.
  Qed.
  
  (* tgt Mod ⊆ cancelled Mod *)
  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H; eauto using tgt_wf. clear H; intros [WF H].
    assert (IV:= init_cond_valid). des.
    destruct (H rs); des; et.
    rewrite IV0 /init_cond /MainAS.init_cond /icond_winv {1}winv_split_empty. 
    iIntros ">[[[? ?] ?] ?]". iFrame. et.
  (*SLOW*)Qed.
End MainAll. *)
