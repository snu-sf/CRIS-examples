Require Import CRIS.common.CRIS CRIS.cancellation.Cancel.
From CRIS.promise_free.pfmem Require Import PFMemHeader PFMemA.
From CRIS.promise_free.gpfsl Require Import base.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.pfmem Require Import PFMemA PFMemI PFMemIA.
From CRIS.promise_free.system Require Import
  SystemHeader SystemI SystemA SystemIA SystemTactics.
From CRIS.promise_free.examples Require Import MPI MPA MPIA.
From CRIS.promise_free.lib Require Import Language.

Section MPAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS, _ONESHOT: !one_shotG}.

  Definition lang := Language.mk (λ _ : (), tt) (const False) (λ _ : ProgramEvent.t, λ _ _, True).
  Definition syn : Threads.syntax := IdentMap.singleton 1%positive (existT lang tt).
  Definition init : Configuration.t := Configuration.init syn [].

  Local Definition sp_user_s : specmap := MPA.sp.
  Local Definition smod_src : SMod.t := (MPA.Mod) ☆ (SystemA.Mod sp_user_s ⊤) ☆ (PFMemA.smod).
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_tgt : Mod.t := MPI.t ★ (SystemI.t) ★ (PFMemI.t syn []).

  Local Definition sp : specmap := SMod.sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition SchInSp : (SystemA.sp sp_user_s ⊤) ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
  Qed.

  Local Definition UserInSp : sp_user_s ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
  Qed.

  Local Definition MainInSp : (MPA.sp) ⊆ sp_user_s. Proof. refl. Qed.
  Local Definition init_cond : iProp Σ := PFMemA.init_cond ∗ SystemA.init_cond [].

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    tview_sys_gen 1 1 0 (TView.init []) ∗ Cancel.init_res ⊢
      refines mod_src mod_top.
  Proof.
    iIntros "[TV INIT]".
    iApply refines_trans. iSplitR.
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { apply SMod.cancellable_add; last apply SMod.cancellable_add; r;
        rewrite /= /MPA.fnsems /SystemA.fnsems /PFMemA.fnsems; mod_tac ss.
    }
    { assert (Ht : (SMod.sp_from smod_src).1 !! entry =
                     fsp_some (MPA.main_spec)) by mod_tac.
      rewrite Ht; clear Ht.
      ss; exists tt; split; refl.
    }
    { unfoldPrePost. iIntros "% % [_ [% _]] //". }
    { iDestruct "INIT" as "(TID & YIELD & WINV & $ & $)".
      unfoldPrePost. iFrame; eauto.
    }
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "[MEM SYS]".
    iApply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src !SMod.to_mod_add.
    (* abstraction of Mem *)
    iApply ctxr_trans. iSplitL "MEM".
    { do 2 ctxr_drop.
      iApply PFMemIA.ctxr. iExact "MEM".
    }
    (* abstraction of Sch *)
    iApply ctxr_trans. iSplitL "SYS".
    { ctxr_drop.
      iApply SystemIA.ctxr.
      - apply UserInSp.
      - apply SchInSp.
      - et.
      - iExact "SYS".
    }
    (* abstraction of MP *)
    ctxr_norm. iApply MPIA.ctxr.
    - apply SchInSp.
    - apply MainInSp.
  (*SLOW*)Qed.

  Lemma top_tgt :
    init_cond ∗ tview_sys_gen 1 1 0 (TView.init []) ∗ Cancel.init_res ⊢
      refines mod_tgt mod_top.
  Proof.
    iIntros "(INIT & TV & CANCEL)".
    iApply refines_trans. iSplitL "INIT".
    - iApply src_tgt; iFrame.
    - iApply cancel_src; iFrame.
  Qed.

  Ltac wf_solver :=
    let rec go :=
      (apply Mod.add_wf; [go|go|rewrite ?Mod.dom_fnsems_add; set_solver|prove_nodup; set_solver])
      || (econs; eauto; [mod_tac|prove_nodup]) in
    go.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    eapply Mod.add_wf.
    { econs; eauto; [mod_tac|prove_nodup]. }
    { eapply Mod.add_wf.
      { econs; eauto; [mod_tac|prove_nodup]. }
      { econs; eauto; [mod_tac|prove_nodup]. }
      { mod_tac. }
      { prove_nodup; set_solver. }
    }
    { mod_tac. }
    { prove_nodup; set_solver. }
  Qed.
End MPAux.

Module MPAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; histΓ; atomicΓ; sysΓ; one_shotΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : histGS) (_ : sysGS)
      src_res tgt_res,
        refines_lmod
          (Mod.to_lmod mod_tgt tgt_res)
          (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV H0])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINV_empty]".
    iMod hist_alloc as "(% & MEM & TV)".
    iMod (sys_alloc with "TV") as "(% & SYS & TV)".
    do 6 iExists _.
    iPoseProof (top_tgt with "[WINV H0 MEM SYS TV]") as "REF".
    { rewrite /init_cond /Cancel.init_res.
      iDestruct "H0" as "(TID & YIELD & TIDAUTH & YIELDAUTH)".
      iFrame.
    }
    iAssert (⌜∃ src_res, ✓ src_res /\
      refines_lmod (Mod.to_lmod mod_tgt ε) (Mod.to_lmod mod_top src_res)⌝)%I
      with "[WINV_empty REF]" as "%Href".
    { iApply refines_adequacy. { exact tgt_wf. } iFrame. }
    destruct Href as [src_res [_ Href]].
    iPureIntro. exists src_res, ε. exact Href.
  (*SLOW*)Qed.
End MPAll.
