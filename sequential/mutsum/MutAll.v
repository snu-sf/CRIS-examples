From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.mutsum Require Import MutHeader MutFA MutGA MutMainA.
From CRIS.mutsum Require Import MutFI MutGI MutMainI.
From CRIS.mutsum Require Import MutFIAproof MutGIAproof MutMainIAproof.
From CRIS.apc Require Import APCHeader APC APCI APCA APCC.
From CRIS.apc Require Import APCIAproof APCACproof.

Section MutAll.
  Context `{!crisG Γ Σ α β τ Hsub Hinv}.

  Local Definition smod_src : SMod.t := MutMainA.smod false ☆ MutFA.smod ☆ MutGA.smod ☆ APCC.smod.
  Local Definition sp : specmap := SMod.sp_from smod_src.

  Local Definition smod_pure : SMod.t := MutFA.smod ☆ MutGA.smod.
  Local Definition sp_pure : specmap := MutFA.SpF ∪ MutGA.SpG.

  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.
  Local Definition mod_tgt : Mod.t := MutMainI.t ★ MutFI.t ★ MutGI.t ★ APCI.t.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    Cancel.init_res ⊢ refines mod_src mod_top.
  Proof.
    iIntros "Hinit".
    iApply refines_trans. iSplitR "Hinit".
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { repeat apply SMod.cancellable_add; r; mod_tac ss. }
    { assert (Ht : (SMod.sp_from smod_src).1 !! entry = fsp_none) by mod_tac.
      rewrite Ht; clear Ht.
      ss; exists tt; split; refl.
    }
    { unfoldPrePost. iIntros "% % $ //". }
    iDestruct "Hinit" as "(X & Y & Z & $ & $)".
    unfoldPrePost; done.
  Qed.

  Lemma apc_in_sp : APCA.sp ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq. mod_tac.
  Qed.

  Lemma mutf_in_pure : MutFA.SpF ⊆ sp_pure.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq. mod_tac.
  Qed.

  Lemma mutg_in_pure : MutGA.SpG ⊆ sp_pure.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq. mod_tac.
  Qed.

  Lemma pure_in_sp : sp_pure ⊆ sp.
  Proof.
    split; et.
    rewrite /sp_pure. eapply (map_union_least MutFA.SpF.1 MutGA.SpG.1); try refl.
    - repeat try eapply insert_subseteq_l; last apply map_empty_subseteq. mod_tac.
    - repeat try eapply insert_subseteq_l; last apply map_empty_subseteq. mod_tac.
  Qed.
  
  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : ⊢ refines mod_tgt mod_src.
  Proof.
    iApply ctxr_refines.
    rewrite /mod_src /mod_tgt !SMod.to_mod_add.

    (* abstraction of APCI to APCA *)
    iApply ctxr_trans. iSplitR.
    { do 3 ctxr_drop. iApply APCIA.ctxr. }

    (* abstraction of MutF *)
    iApply ctxr_trans. iSplitR.
    { ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
      iApply (MutFIA.ctxr (Sp:=sp) (SpPure:=sp_pure)).
      { eapply apc_in_sp. }
      { eapply mutg_in_pure. }
      { eapply pure_in_sp. }
      iEmpIntro.
    }

    (* abstraction of MutG *)
    iApply ctxr_trans. iSplitR.
    { ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
      iApply (MutGIA.ctxr (Sp:=sp) (SpPure:=sp_pure)).
      { eapply apc_in_sp. }
      { eapply mutf_in_pure. }
      { eapply pure_in_sp. }
      iEmpIntro.
    }

    (* abstraction of MutMain *)
    iApply ctxr_trans. iSplitR.
    { ctxr_rotate. do 2 ctxr_drop. ctxr_rotate.
      iApply (MutMainIA.ctxr (Sp:=sp) (SpPure:=sp_pure)).
      { eapply apc_in_sp. }
      { eapply mutf_in_pure. }
      { eapply pure_in_sp. }
    }
    
    (* abstraction of APCA to APCC *)
    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_rotate. ctxr_drop. iApply APCAC.ctxr.
      { eapply apc_in_sp. }
      { eapply pure_in_sp. }
      { i; ss.
        rewrite /sp_pure lookup_union in H.
        destruct (String.eq_dec fn MutHdr.mutf.1).
        { subst. rewrite lookup_insert lookup_insert_ne // lookup_empty in H. inv H. esplits; eauto. }
        destruct (String.eq_dec fn MutHdr.mutg.1).
        { subst. rewrite lookup_insert lookup_insert_ne // lookup_empty in H. inv H. esplits; eauto. }
        rewrite !lookup_insert_ne // in H; ii; inv H.
      }
    }

    (* elimination of pure cCall *)
    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_rotate. do 2 ctxr_drop.
      iApply (MutMainIA.ctxr_close (Sp:=sp) (SpPure:=sp_pure)).
      { eapply apc_in_sp. }
      { eapply mutf_in_pure. }
      { eapply pure_in_sp. }
    }

    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_rotate. ctxr_swap. ctxr_rotate. ctxr_refl. }

    rewrite /MutMainA.t /MutFA.t /MutGA.t /APCC.t.
    ctxr_refl.
  (*SLOW*)Qed.

  Lemma top_tgt :
    Cancel.init_res ⊢ refines mod_tgt mod_top.
  Proof.
    iIntros "Hinit".
    iApply refines_trans. iSplitR "Hinit".
    { iApply src_tgt. }
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
End MutAll.

Module MutAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) src_res tgt_res,
      refines_lmod
        (Mod.to_lmod mod_tgt tgt_res)
        (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV Hinit])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINVempty]".
    iExists _, _, _, _.
    iPoseProof (top_tgt with "[WINV Hinit]") as "REF".
    { rewrite /Cancel.init_res.
      iDestruct "Hinit" as "(H0 & H1 & H2 & H3)". iFrame.
    }
    iAssert (⌜∃ src_res, ✓ src_res /\
      refines_lmod (Mod.to_lmod mod_tgt ε) (Mod.to_lmod mod_top src_res)⌝)%I
      with "[WINVempty REF]" as "%Href".
    { iApply refines_adequacy. { eapply tgt_wf. } iFrame. }
    destruct Href as [src_res [_ Href]].
    iPureIntro. exists src_res, ε. exact Href.
  (*SLOW*)Qed.
End MutAll.
(* Print Assumptions MutAll.behavioral_refinement. *)
