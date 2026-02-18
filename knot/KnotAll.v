Require Import CRIS Cancel CallFilter.
Require Import MemHeader MemI MemA MemIAproof.
Require Import APCHeader APC APCI APCA APCC APCACproof APCIAproof.
Require Import KnotHeader KnotMainHeader KnotI KnotMainI.
Require Import KnotA KnotMainA.
Require Import KnotIAproof KnotMainIAproof.

Section KnotAux.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, _MEM: !memGS, _KNOT: !knotGS}.

  (* mem *)
  Local Definition csl : string → bool := λ _, false.
  (* global environment *)
  Local Definition genv : GEnv.t := KnotGEnv.t ++ KnotMainGEnv.t.

  (* pure sp *)
  Local Definition sp_rec : specmap := KnotA.knot_rec_sp.
  Local Definition sp_fun : specmap := KnotMainA.main_fun_sp genv sp_rec.
  Local Definition sp_pure : specmap := KnotMainA.main_fun_sp genv sp_rec ∪ KnotA.knot_rec_sp.

  Local Definition smod_src : SMod.t :=
    (KnotMainA.smod genv sp_rec false) ☆ (KnotA.smod genv sp_rec sp_fun) ☆ APCC.smod.
  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.
  Local Definition mod_tgt : Mod.t := KnotMainI.t genv ★ KnotI.t genv ★ MemI.t csl genv ★ APCI.t.

  Local Lemma genv_wf : GEnv.wf genv. Proof. cbn. prove_nodup. Qed.

  Local Definition init_cond : iProp Σ := KnotA.init_cond genv ∗ MemA.init_cond csl genv.

  Lemma cancel_src :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ KnotA.knot_frag None ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { repeat apply SMod.cancellable_add; r; mod_tac ss. }
    { assert (Ht : (SMod.conc_sp_from smod_src).1 !! entry =
                     fsp_some (KnotMainA.main_spec)) by mod_tac.
      eexists _, _; splits.
      { ss; exists (tt); split; refl. }
      { iIntros "[? [? [? $]]]"; ss. }
      { unfold_pre_post. iIntros "% % [% %] //". }
    }
  Qed.

  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt !SMod.to_mod_add.

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 3 ctxr_drop. eapply MemIA.ctxr. }
    (* abstraction of APCI to APCA *)
    etrans; cycle 1.
    { ctxr_rotate. do 3 ctxr_drop. eapply APCIA.ctxr. }
    (* abstraction of Knot *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply KnotIA.ctxr with (sp:=sp) (sp_pure:=sp_pure) (sp_rec:=sp_rec) (sp_fun:=sp_fun); eauto.
      { eapply genv_wf. }
      { unfold genv. eapply incl_appl; refl. }
      { split; et.
        repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
      }
      { split; et. apply map_union_subseteq_l. }
      { split; et. apply map_union_least; repeat try eapply insert_subseteq_l; try apply map_empty_subseteq; mod_tac.
      }
    }
    (* abstraction of KnotMain *)
    etrans; cycle 1.
    { ctxr_norm. eapply KnotMainIA.ctxr; eauto.
      { eapply genv_wf. }
      { unfold genv. eapply incl_appr; refl. }
      { split; et.
        repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
      }
      { split; et.
        repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
      }
      { split; et.
        apply map_union_subseteq_r.
        rewrite /KnotMainA.main_fun_sp /KnotA.knot_rec_sp.
        apply map_disjoint_insert_l_2; simpl_map; auto with map_disjoint.
      }
      { split; et.
        apply map_union_least; repeat try eapply insert_subseteq_l; try apply map_empty_subseteq; mod_tac.
      }
    }
    (* abstraction of APCA to APCC *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_drop.
      eapply APCAC.ctxr.
      { split; et.
        repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
      }
      { split; et.
        apply map_union_least; repeat try eapply insert_subseteq_l; try apply map_empty_subseteq; mod_tac.
      }
      { rewrite /sp_pure /KnotMainA.main_fun_sp /KnotA.knot_rec_sp.
        intros ? ? [?H|?H]%lookup_union_Some;
          try rewrite lookup_singleton_Some in H; des; clarify.
        { rewrite /find_body; simpl_map. esplits; eauto. }
        { rewrite /find_body; simpl_map; esplits; eauto. }
        clear H0. apply map_disjoint_insert_l_2; simpl_map; auto with map_disjoint.
      }
    }
    (* elimination of pure call *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 2 ctxr_drop. ctxr_rotate.
      eapply KnotMainIA.ctxr_close with (sp:=sp) (sp_pure:=sp_pure) (sp_fun:=sp_fun); eauto.
      { eapply genv_wf. }
      { unfold genv. eapply incl_appr; refl. }
      { split; et.
        repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
      }
      { split; et.
        repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
      }
      { split; et.
        apply map_union_subseteq_r.
        rewrite /KnotMainA.main_fun_sp /KnotA.knot_rec_sp.
        apply map_disjoint_insert_l_2; simpl_map; auto with map_disjoint.
      }
      { split; et.
        apply map_union_least; repeat try eapply insert_subseteq_l; try apply map_empty_subseteq; mod_tac.
      }
    }
    (* elimination of mem *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 3 ctxr_drop. eapply elim_module. }
    rewrite right_id.

    etrans; cycle 1.
    { ctxr_swap. ctxr_rotate. ctxr_refl. }

    eapply ctxr_cond_strengthen.
    iIntros "[$ $]".
  Unshelve. exact ∅.
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines
      (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ KnotA.knot_frag None ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
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
End KnotAux.

Module KnotAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ; knotΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : knotGS) (_ : memGS)
      src_res tgt_res,
      refines_lmod
        (Mod.to_lmod mod_top src_res)
        (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "[% [% [% [% ?]]]]".
    iMod (knot_alloc ) as "[% [? ?]]".
    iMod (mem_alloc csl genv) as "[% ?]".
    iExists _, _, _, _, _, _.
    pose proof (top_tgt tgt_wf) as Href.
    iStopProof. eapply entails_pointwise; iIntros (res Hres) "R".
    iPoseProof (Own_valid with "R") as "%".
    rewrite /refines in Href; hexploit Href; eauto using tgt_wf.
    clear Href; intros [? Href].
    iPureIntro; hexploit (Href res); eauto.
    { rewrite Hres; iIntros "[[W [$ [$ [$ $]]]] [$ [$ [$ ?]]]]".
      rewrite {1}winv_split_empty comm //. iDestruct "W" as "[$ $]".
      rewrite /KnotA.var_points_to /mem_init_val /genv /KnotGEnv.t /KnotMainGEnv.t.
      Local Transparent CEnv.id2blk CEnv.load_genv.
      rewrite /CEnv.id2blk /CEnv.load_genv /=.
      iApply (own_update with "[$]").
      apply cmra_update_included, mem_init_auth_r_valid.
      rewrite /mem_init_val /=. hss.
    }
    s; i; des; et.
  (*SLOW*)Qed.
End KnotAll.

(* Print Assumptions KnotAll.behavioral_refinement. *)
