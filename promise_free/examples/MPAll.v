Require Import CRIS Cancel.
Require Import PFMemHeader PFMemA base HistoryRA AtomicRA PFMemA PFMemI PFMemIA.
Require Import SystemHeader SystemI SystemA SystemIA SystemTactics.
Require Import MPI MPA MPIA.
Require Import Language.

Section MPAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS, _ONESHOT: !one_shotG}.

  Definition lang := Language.mk (λ _ : (), tt) (const False) (λ _ : ProgramEvent.t, λ _ _, True).
  Definition syn : Threads.syntax := IdentMap.singleton 1%positive (existT lang tt).
  Definition init : Configuration.t := Configuration.init syn [].

  Local Definition sp_user_s : specmap := MPA.sp.
  Local Definition smod_src : SMod.t := (MPA.Mod) ☆ (SystemA.Mod sp_user_s ⊤) ☆ (PFMemA.smod).
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_tgt : Mod.t := MPI.t ★ (SystemI.t) ★ (PFMemI.t syn []).

  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
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
    refines
      (mod_src, init_cond)
      (mod_top, init_cond ∗ tview_sys_gen 1 1 0 (TView.init []) ∗ Cancel.init_res)%I.
  Proof.
    etrans. { eapply ctxr_refines, Cancel.cancellation_prepare; et; clarify. }
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add; last apply SMod.cancellable_add; r;
        rewrite /= /MPA.fnsems /SystemA.fnsems /PFMemA.fnsems; mod_tac ss.
    }
    { assert (Ht : (SMod.conc_sp_from smod_src).1 !! entry =
                     fsp_some (MPA.main_spec)) by mod_tac.
      rewrite Ht; clear Ht.
      eexists _, _; splits.
      { ss; exists tt; split; refl. }
      { iIntros "[$ [$ [$ $]]]"; ss. }
      { unfoldPrePost. iIntros "% % [_ [% _]] //". }
    }
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_tgt, emp%I) (mod_src, init_cond).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src !SMod.to_mod_add.
    (* abstraction of Mem *)
    etrans.
    { do 2 ctxr_drop.
      eapply PFMemIA.ctxr.
    }
    (* abstraction of Sch *)
    etrans.
    { ctxr_drop.
      eapply SystemIA.ctxr.
      - apply UserInSp.
      - apply SchInSp.
      - et.
    }
    (* abstraction of MP *)
    etrans.
    { ctxr_norm. eapply MPIA.ctxr.
      - apply SchInSp.
      - apply MainInSp.
    }
    eapply ctxr_consequence.
    { iIntros "[? [? ?]]". iFrame. }
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines
      (mod_tgt, emp%I)
      (mod_top, init_cond ∗ tview_sys_gen 1 1 0 (TView.init []) ∗ Cancel.init_res)%I.
  Proof.
    etrans.
    { eapply src_tgt. }
    { eapply cancel_src. }
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
      { rewrite ?Mod.dom_fnsems_add; set_solver. }
      { prove_nodup; set_solver. }
    }
    { rewrite ?Mod.dom_fnsems_add; set_solver. }
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
    iMod cris_alloc as "[% [% [% [% ?]]]]".
    iMod hist_alloc as "[% [? TV]]".
    iMod (sys_alloc with "TV") as "[% [? ?]]".
    do 6 iExists _.
    pose proof (top_tgt) as Href.
    iStopProof. eapply entails_pointwise; iIntros (res Hres) "R".
    iPoseProof (Own_valid with "R") as "%".
    rewrite /refines in Href; hexploit Href; eauto using tgt_wf.
    clear Href; intros [? Href].
    iPureIntro; hexploit (Href res); eauto.
    { rewrite Hres; iIntros "[[W [$ [$ [$ $]]]] [[$ $] [$ $]]]".
      rewrite {1}winv_split_empty comm //.
    }
    s; i; des; et.
  (*SLOW*)Qed.
End MPAll.
