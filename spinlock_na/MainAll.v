Require Import CRIS.
Require Import LockHeader LockI LockA LockIA MainI MainA MainIA.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SchHeader SchI SchA SchIAproof.
Require Import Cancel.

(* Cancellation *)
Section MainAux.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, _MEM: !memGS, _SCH: !schGS, _SPINLOCK: !spinlockG, _SPINLOCKMAIN: !spinlockmainG}.
  Context (csl : string → bool) (genv : GEnv.t).
  (* sp of source module (scheduler spec excluded) *)
  Local Definition sp_user : specmap := MainA.sp ⊤.

  (* the source SMod *)
  Local Definition smod_src : SMod.t := MainA.smod nroot ☆ SchA.smod sp_user ⊤.
  (* the top-level module after cancellation *)
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  (* the target module *)
  Local Definition mod_tgt : Mod.t := SpinLockMainI.t ★ SpinLockI.t ★ MemI.t csl genv ★ SchI.t .

  (* the source sp *)
  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  (* the source Mod *)
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  (* initial condition for the source *)
  Local Definition init_cond : iProp Σ := (MemA.init_cond csl genv ∗ SchA.init_cond)%I.

  (* Some assumptions on sp inclusion *)
  Lemma SchInSp : (SchA.sp sp_user ⊤) ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
  Qed.

  Lemma MainInSp : MainA.sp ⊤ ⊆ sp_user.
  Proof.
    split; et.
  Qed.

  Lemma UserInSp : sp_user ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq.
    rewrite !lookup_omap !lookup_fmap !lookup_omap lookup_union_with /MainA.fnsems /SchA.fnsems.
    simpl_map; ss.
    rewrite nclose_nroot //.
  Qed.

  (* Refinement between smod_cancel and smod_src *)
  Lemma cancel_src :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TidFrag 0 0 ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add; r; rewrite /= /MainA.fnsems /SchA.fnsems; mod_tac ss. }
    { assert (Ht : (SMod.conc_sp_from smod_src).1 !! entry =
                     fsp_some (fspec_sch (↑nroot) fspec_trivial)) by mod_tac.
      rewrite Ht; clear Ht.
      eexists _, _; splits.
      { ss; exists (0, 0, tt); split; refl. }
      { rewrite !nclose_nroot. iIntros "[$ [$ [$ $]]]"; ss. }
      { unfold_pre_post. iIntros "% % [_ [_ $]]". }
    }
  Qed.

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    apply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt /init_cond.

    (* abstraction of Sch *)
    etrans; cycle 1.
    { do 3 ctxr_drop.
      eapply SchIA.ctxr.
      - apply SchInSp.
      - apply UserInSp.
      - et.
    }

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 3 ctxr_drop.
      eapply MemIA.ctxr.
    }

    (* abstraction of SpinLock *)
    etrans; cycle 1.
    { do 2 ctxr_drop.
      eapply LockIA.ctxr; cycle 1.
      - apply SchInSp.
      - set_solver.
    }

    (* abstraction of SpinLockMain *)
    etrans; cycle 1.
    { ctxr_drop.
      rewrite -nclose_nroot.
      eapply MainIA.ctxr; rewrite ?nclose_nroot.
      - apply SchInSp.
      - apply SchInSp.
      - apply MainInSp.
    }

    (* elimination of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_drop. eapply elim_module. }
    rewrite right_id.

    (* elimination of SpinLock *)
    etrans; cycle 1.
    { do 2 ctxr_drop. eapply elim_module. }
    rewrite right_id.

    etrans; cycle 1.
    { ctxr_rotate. refl. }

    rewrite /MainA.t /SchA.t. unseal CRIS.
    rewrite SMod.to_mod_add.
    eapply ctxr_cond_strengthen; et.
  (*SLOW*)Qed.

  (* source Mod ⊆ source SMod ⊆ cancelled Mod *)
  Lemma cancel_tgt :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TidFrag 0 0 ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt; eapply Mod.add_wf.
    { econs; eauto; [mod_tac|prove_nodup]. }
    { eapply Mod.add_wf.
      { econs; eauto; [mod_tac|prove_nodup]. }
      { eapply Mod.add_wf.
        { econs; eauto; [mod_tac|prove_nodup]. }
        { econs; eauto; [mod_tac|prove_nodup]. }
        { set_solver. }
        { ss; prove_nodup; set_solver. }
      }
      { rewrite Mod.dom_fnsems_add; set_solver. }
      { prove_nodup; set_solver. }
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { prove_nodup; set_solver. }
  Qed.
End MainAux.

Module MainAll.
  Import inv_instances.

  (* initialization parameters for memory module *)
  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  (* HRA & GRA *)
  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ; newschΓ; spinlockΓ; spinlockmainΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ].

  (* tgt Mod ⊆ cancelled Mod *)
  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : schGS) (_ : memGS)
      src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod (mod_tgt csl genv) tgt_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "[% [% [% [% ?]]]]".
    iMod sch_alloc as "[% ?]".
    iMod (mem_alloc csl genv) as "[% ?]".
    iExists _, _, _, _, _, _.
    pose proof (cancel_tgt csl genv) as Href.
    iStopProof. eapply entails_pointwise; iIntros (res Hres) "R".
    iPoseProof (Own_valid with "R") as "%".
    rewrite /refines in Href; hexploit Href; eauto using tgt_wf.
    clear Href; intros [? Href].
    iPureIntro; hexploit (Href res); eauto.
    { rewrite Hres. iIntros "[[W [$ [$ [$ $]]]] [[$ $] [$ _]]]".
      rewrite {1}winv_split_empty comm //.
    }
    s; i; des; et.
  (*SLOW*)Qed.
End MainAll.
