Require Import CRIS Cancel SMod CallFilter.
Require Import MemI MemA MemIAproof ImpPrelude.
Require Import SchHeader SchI SchA SchIAproof SchTactics.
Require Import FaaHeader ClientI ClientA ClientIA FaaI FaaA FaaIA.

Section ClientAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _MEM: !memGS, _SCH: !schGS, _INCR: !incrG}.
  Context (csl : string → bool) (genv : GEnv.t).

  (* source module *)
  Local Definition sp_user_s : specmap := ClientA.sp nroot.
  Local Definition smod_src : SMod.t := (ClientA.smod nroot) ☆ (SchA.smod sp_user_s ⊤).
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_tgt : Mod.t := ClientI.t ★ FaaI.t ★ (MemI.t csl genv) ★ (SchI.t).

  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition SchInSp : (SchA.sp sp_user_s ⊤) ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
  Qed.
  Local Definition UserInSp : sp_user_s ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
  Qed.
  Local Definition MainInSp : (ClientA.sp nroot) ⊆ sp_user_s.
  Proof. by reflexivity. Qed.

  Local Definition init_cond : iProp Σ :=
    MemA.init_cond csl genv ∗ SchA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines
      (mod_top, init_cond ∗ TidFrag 0 0 ∗ Cancel.init_res)%I
      (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add; r; rewrite /= /ClientA.fnsems /SchA.fnsems; mod_tac ss. }
    { assert (Ht : (SMod.conc_sp_from smod_src).1 !! entry =
                     fsp_some (fspec_sch (↑nroot) fspec_trivial)) by mod_tac.
      rewrite Ht; clear Ht.
      eexists _, _; splits.
      { ss; exists (0, 0, tt); split; refl. }
      { rewrite !nclose_nroot. iIntros "[$ [$ [$ $]]]"; ss. }
      { unfoldPrePost. iIntros "% % [_ [_ $]]". }
    }
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src.

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

    (* abstraction of Faa *)
    etrans; cycle 1.
    { do 2 ctxr_drop.
      eapply main_adequacy, FaaIA.sim.
    }
    rewrite /FaaIA.FaaIA.MA.
    
    (* abstraction of Incr *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply ClientIA.ctxr; cycle 2.
      - apply MainInSp.
      - rewrite nclose_nroot. apply SchInSp.
    }

    etrans; cycle 1.
    { ctxr_rotate. ctxr_refl. }

    (* elimination of mem *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 2 ctxr_drop. eapply elim_module. }
    rewrite right_id.

    rewrite /SchIAproof.SchIA.SchAMod.
    rewrite /SchA.t /ClientA.t /MemA.t.
    unseal CRIS.
    ctxr_rotate.
    rewrite SMod.to_mod_add /init_cond //.
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond ∗ TidFrag 0 0 ∗ Cancel.init_res)%I
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
        { prove_nodup; set_solver. }
      }
      { rewrite Mod.dom_fnsems_add; set_solver. }
      { prove_nodup; set_solver. }
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { prove_nodup; set_solver. }
  Qed.
End ClientAux.

Module ClientAll. 
  Import inv_instances.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ; newschΓ; incrΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ].

  Lemma behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : schGS) (_ : memGS)
      src_res tgt_res,
    refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod (mod_tgt csl genv) tgt_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "[% [% [% [% ?]]]]".
    iMod sch_alloc as "[% ?]".
    iMod (mem_alloc csl genv) as "[% ?]".
    iExists _, _, _, _, _, _.
    pose proof (top_tgt csl genv) as Href.
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
End ClientAll.

(* Print Assumptions ClientAll.behavioral_refinement. *)
