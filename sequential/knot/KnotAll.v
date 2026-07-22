From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.filter Require Import CallFilter.
From CRIS.imp_system.mem Require Import MemHeader MemI MemA MemIAproof.
From CRIS.apc Require Import APCHeader APC APCI APCA APCC APCACproof APCIAproof.
From CRIS.knot Require Import KnotHeader KnotMainHeader KnotI KnotMainI.
From CRIS.knot Require Import KnotA KnotMainA.
From CRIS.knot Require Import KnotIAproof KnotMainIAproof.

Section KnotAux.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, _MEM: !memGS, _KNOT: !knotGS}.

  (* global environment *)
  Local Definition genv : GEnv.t := KnotGEnv.t ++ KnotMainGEnv.t.

  (* pure sp *)
  Local Definition sp_rec : specmap := KnotA.knot_rec_sp.
  Local Definition sp_fun : specmap := KnotMainA.main_fun_sp genv sp_rec.
  Local Definition sp_pure : specmap := KnotMainA.main_fun_sp genv sp_rec ∪ KnotA.knot_rec_sp.

  Local Definition smod_src : SMod.t :=
    (KnotMainA.smod genv sp_rec false) ☆ (KnotA.smod genv sp_rec sp_fun) ☆ APCC.smod.
  Local Definition sp : specmap := SMod.sp_from smod_src.
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.
  Local Definition mod_tgt : Mod.t := KnotMainI.t genv ★ KnotI.t genv ★ MemI.t genv ★ APCI.t.

  Local Lemma genv_wf : GEnv.wf genv. Proof. cbn. prove_nodup. Qed.

  Local Definition init_cond : iProp Σ := KnotA.init_cond genv ∗ MemA.init_cond genv.

  Lemma cancel_src :
    KnotA.knot_frag None ∗ Cancel.init_res ⊢
      refines mod_src mod_top.
  Proof.
    iIntros "[Hknot Hinit]".
    iApply refines_trans. iSplitR "Hknot Hinit".
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { repeat apply SMod.cancellable_add; r; mod_tac ss. }
    { assert (Ht : (SMod.sp_from smod_src).1 !! entry =
                     fsp_some (KnotMainA.main_spec)) by mod_tac.
      rewrite Ht; clear Ht. ss; exists tt; split; refl.
    }
    { unfoldPrePost. iIntros "% % [% %] //". }
    iDestruct "Hinit" as "(X & Y & Z & $ & $)".
    unfoldPrePost. iSplit; et.
  Qed.

  Lemma src_tgt : init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "[HKnot HMem]".
    iApply ctxr_refines.
    rewrite /mod_src /mod_tgt !SMod.to_mod_add.

    (* abstraction of Mem *)
    iApply ctxr_trans. iSplitL "HMem".
    { do 3 ctxr_rotate. do 3 ctxr_drop. iApply MemIA.ctxr. iFrame. }
    (* abstraction of APCI to APCA *)
    iApply ctxr_trans. iSplitR "HKnot".
    { ctxr_rotate. do 3 ctxr_drop. iApply APCIA.ctxr. }
    (* abstraction of Knot *)
    iApply ctxr_trans. iSplitL "HKnot".
    { ctxr_drop.
      iApply (KnotIA.ctxr genv sp sp_rec sp_fun sp_pure); eauto.
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
    iApply ctxr_trans. iSplitR.
    { ctxr_norm. iApply (KnotMainIA.ctxr genv sp sp_rec sp_fun sp_pure); eauto.
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
    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_rotate. ctxr_drop.
      iApply APCAC.ctxr.
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
    (* elimination of pure cCall *)
    iApply ctxr_trans. iSplitR.
    { do 3 ctxr_rotate. do 2 ctxr_drop. ctxr_rotate.
      iApply (KnotMainIA.ctxr_close genv sp sp_rec sp_fun sp_pure); eauto.
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
    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_rotate. do 3 ctxr_drop. iApply elim_module. }
    rewrite right_id.

    iApply ctxr_trans. iSplitR.
    { ctxr_swap. ctxr_rotate. ctxr_refl. }

    ctxr_refl.
  (*SLOW*)Qed.

  Lemma top_tgt :
    init_cond ∗ KnotA.knot_frag None ∗ Cancel.init_res ⊢
      refines mod_tgt mod_top.
  Proof.
    iIntros "(Hinit & Hknot & Hcancel)".
    iApply refines_trans. iSplitL "Hinit".
    { iApply src_tgt. iFrame. }
    iApply cancel_src. iFrame.
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
        { prove_nodup; set_solver. }
      }
      { mod_tac. }
      { prove_nodup; set_solver. }
    }
    { mod_tac. }
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
        (Mod.to_lmod mod_tgt tgt_res)
        (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV Hinit])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINVempty]".
    iMod knot_alloc as "(% & HKnotFull & HKnotFrag)".
    iMod (mem_alloc genv) as "(% & HMem)".
    iExists _, _, _, _, _, _.
    iDestruct "HMem" as "[HMemAuth HMemFrag]".
    iPoseProof (own_update with "HMemFrag") as ">Hvar".
    { apply cmra_update_included.
      apply (mem_init_auth_r_valid genv 2 0%Z 0%Z).
      rewrite /mem_init_val /genv /KnotGEnv.t /KnotMainGEnv.t.
      Local Transparent CEnv.id2blk CEnv.load_genv.
      rewrite /CEnv.id2blk /CEnv.load_genv /=. cSimpl.
    }
    iPoseProof (top_tgt with
      "[WINV Hinit HKnotFull HKnotFrag HMemAuth Hvar]") as "REF".
    { rewrite /init_cond /KnotA.init_cond /MemA.init_cond /Cancel.init_res.
      iDestruct "Hinit" as "(HTID & HYIELD & HTIDAUTH & HYIELDAUTH)".
      iFrame "WINV HTID HYIELD HTIDAUTH HYIELDAUTH HKnotFull HKnotFrag HMemAuth".
      rewrite /KnotA.var_points_to /mem_init_val /genv /KnotGEnv.t /KnotMainGEnv.t.
      Local Transparent CEnv.id2blk CEnv.load_genv.
      rewrite /CEnv.id2blk /CEnv.load_genv /=.
      iFrame.
    }
    iAssert (⌜∃ src_res, ✓ src_res /\
      refines_lmod (Mod.to_lmod mod_tgt ε) (Mod.to_lmod mod_top src_res)⌝)%I
      with "[WINVempty REF]" as "%Href".
    { iApply refines_adequacy. { eapply tgt_wf. } iFrame. }
    destruct Href as [src_res [_ Href]].
    iPureIntro. exists src_res, ε. exact Href.
  (*SLOW*)Qed.
End KnotAll.

(* Print Assumptions KnotAll.behavioral_refinement. *)
