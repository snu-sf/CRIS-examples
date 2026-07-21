Require Import CRIS.common.CRIS.
From CRIS.spinlock Require Import LockHeader LockI LockA LockIA MainI MainA.
From CRIS.spinlock Require Import MainIA.
From CRIS.imp_system Require Import imp.ImpPrelude mem.MemI mem.MemA.
From CRIS.imp_system Require Import mem.MemIAproof.
From CRIS.scheduler Require Import SchHeader SchI SchA SchIAproof.
Require Import CRIS.cancellation.Cancel.

(* Cancellation *)
Section MainAux.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !schGS, !spinlockG, !spinlockmainG}.
  Context (genv : GEnv.t).
  (* sp of source module (scheduler spec excluded) *)
  Local Definition sp_user : specmap := MainA.sp ⊤.

  (* the source SMod *)
  Local Definition smod_src : SMod.t := MainA.smod nroot ☆ SchA.smod sp_user ⊤.
  (* the top-level module after cancellation *)
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  (* the target module *)
  Local Definition mod_tgt : Mod.t := SpinLockMainI.t ★ SpinLockI.t ★ MemI.t genv ★ SchI.t .

  (* the source sp *)
  Local Definition sp : specmap := SMod.sp_from smod_src.
  (* the source Mod *)
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  (* initial condition for the source *)
  Local Definition init_cond : iProp Σ := (MemA.init_cond genv ∗ SchA.init_cond)%I.

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
    TidFrag 0 0 ∗ Cancel.init_res ⊢ refines mod_src mod_top.
  Proof.
    iIntros "[H1 H2]".
    iApply refines_trans. iSplitR.
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { apply SMod.cancellable_add; r; rewrite /= /MainA.fnsems /SchA.fnsems; mod_tac ss. }
    { ss; exists (0, 0, tt); split; refl. }
    { unfoldPrePost. iIntros "% % [_ [_ $]]". }
    { iDestruct "H2" as "(TID & YIELD & WINV & $ & $)".
      unfoldPrePost. rewrite /SchA.Tid !nclose_nroot. iFrame; eauto.
    }
  Qed.

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "[HMEM HSCH]".
    iApply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt.

    (* abstraction of Sch *)
    iApply ctxr_trans. iSplitL "HSCH".
    { do 3 ctxr_drop.
      iApply SchIA.ctxr.
      - apply SchInSp.
      - apply UserInSp.
      - et.
      - iExact "HSCH".
    }

    (* abstraction of Mem *)
    iApply ctxr_trans. iSplitL "HMEM".
    { do 3 ctxr_rotate. do 3 ctxr_drop.
      iApply MemIA.ctxr.
      iExact "HMEM".
    }

    (* abstraction of SpinLock *)
    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_drop.
      iApply LockIA.ctxr; cycle 1.
      - apply SchInSp.
      - set_solver.
    }

    (* abstraction of SpinLockMain *)
    iApply ctxr_trans. iSplitR.
    { ctxr_drop.
      rewrite -nclose_nroot.
      iApply MainIA.ctxr; rewrite ?nclose_nroot.
      - apply SchInSp.
      - apply SchInSp.
      - apply MainInSp.
    }

    (* elimination of Mem *)
    iApply ctxr_trans. iSplitR.
    { do 3 ctxr_drop. iApply elim_module. }
    rewrite right_id.

    (* elimination of SpinLock *)
    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_drop. iApply elim_module. }
    rewrite right_id.

    iApply ctxr_trans. iSplitR.
    { ctxr_rotate. ctxr_refl. }

    rewrite /MainA.t /SchA.t. unseal CRIS.
    rewrite SMod.to_mod_add.
    iApply ctxr_refl.
  (*SLOW*)Qed.

  (* source Mod ⊆ source SMod ⊆ cancelled Mod *)
  Lemma cancel_tgt :
    init_cond ∗ TidFrag 0 0 ∗ Cancel.init_res ⊢
      refines mod_tgt mod_top.
  Proof.
    iIntros "(H1 & H2 & H3)".
    iApply refines_trans. iSplitL "H1".
    - iApply src_tgt; iFrame.
    - iApply cancel_src; iFrame.
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
        { mod_tac. }
        { ss; prove_nodup; set_solver. }
      }
      { mod_tac. }
      { prove_nodup; set_solver. }
    }
    { mod_tac. }
    { prove_nodup; set_solver. }
  Qed.
End MainAux.

Module MainAll.
  Import inv_instances.

  (* initialization parameters for memory module *)
  Local Definition genv : GEnv.t := GEnv.unit.

  (* HRA & GRA *)
  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ; newschΓ; spinlockΓ; spinlockmainΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ].

  (* tgt Mod ⊆ cancelled Mod *)
  Lemma behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : schGS) (_ : memGS)
       src_res tgt_res,
      refines_lmod
        (Mod.to_lmod (mod_tgt genv) tgt_res)
        (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV HCONC])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINV∅]".
    iMod sch_alloc as "(% & HSCH & HTIDFRAG)".
    iMod (mem_alloc genv) as "(% & HMEM)".
    iExists _, _, _, _, _, _.
    iPoseProof (cancel_tgt genv with "[-WINV∅]") as "REF".
    { iDestruct "HMEM" as "[HMEM _]".
      rewrite /init_cond /Cancel.init_res /MemA.init_cond.
      iFrame.
    }
    iAssert (⌜∃ src_res, ✓ src_res /\ refines_lmod
      (Mod.to_lmod (mod_tgt genv) ε)
      (Mod.to_lmod mod_top src_res)⌝)%I
      with "[WINV∅ REF]" as "%Href".
    { iApply refines_adequacy. { eapply tgt_wf. } iFrame. }
    destruct Href as [src_res [_ Href]].
    iPureIntro. exists src_res, ε. exact Href.
  (*SLOW*)Qed.
End MainAll.
