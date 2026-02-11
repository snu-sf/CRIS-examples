Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonMainI.
Require Import CannonA CannonMainA.
Require Import CannonIAproof CannonMainIAproof.

Section CannonAux.
  Import CannonA.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !concGS, !cannonGS}.
  Local Definition smod_src : SMod.t := CannonA.smod ☆ (MainA.smod 1).
  Local Definition mod_top : Mod.t := (SMod.to_mod ∅ (SMod.cancel smod_src)).
  Local Definition mod_tgt : Mod.t := CannonI.t ★ (MainI.t 1).
  
  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Lemma cancel_src :
    refines (mod_top, Ready ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ Ball ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_src, Ready)%I.
  Proof.
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add; r; rewrite /=; mod_tac ss. }
    { assert (Ht : SMod.conc_sp_from smod_src !! speckey_entry =
        fsp_some (MainA.main_spec)); last (rewrite Ht; clear Ht).
      { rewrite lookup_insert_ne // lookup_kmap_Some; exists None; split; ss. }
       eexists _, _; splits.
      { ss; exists (tt); split; refl. }
      { iIntros "[? [? [? $]]]"; ss. }
      { unfold_pre_post. iIntros "% % %"; by des. }
    }
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, Ready) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src SMod.to_mod_add.

    etrans; cycle 1.
    { ctxr_rotate. ctxr_drop. eapply CannonIA.ctxr. }

    etrans; cycle 1.
    { ctxr_rotate. ctxr_drop. eapply CannonMainIA.ctxr.
      instantiate (1:=sp).
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
        rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
    }

    eapply ctxr_cond_strengthen. by iIntros "$".
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, Ready ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ Ball ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    eapply Mod.add_wf.
    { econs; eauto; [mod_tac|prove_nodup]. }
    { econs; eauto; [mod_tac|prove_nodup]. }
    { set_solver. }
    { prove_nodup; set_solver. }
  Qed.
End CannonAux.

Module CannonAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; concΓ; cannonΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : concGS) (_ : cannonGS)
      src_res tgt_res,
      refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    apply own_admin_soundness.
    iMod winv_alloc as "[% [% [% [% ?]]]]"; iExists _, _, _, _.
    iMod conc_alloc as "[% ?]"; iExists _.
    iMod cannon_alloc as "[% [? ?]]"; iExists _.
    pose proof top_tgt as Href.
    iStopProof. eapply entails_pointwise; iIntros (res Hres) "R".
    iPoseProof (Own_valid with "R") as "%".
    rewrite /refines in Href; hexploit Href; eauto using tgt_wf.
    clear Href; intros [? Href].
    iPureIntro; hexploit (Href res); eauto.
    { rewrite Hres; iIntros "[W [[$ [$ [$ $]]] [$ $]]]".
      rewrite {1}winv_split_empty comm //.
    }
    intros [rt ?].
    exists res, rt; by des.
  Qed.
(*SLOW*)End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)
