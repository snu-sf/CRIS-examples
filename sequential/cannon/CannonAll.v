From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.cannon Require Import CannonHeader CannonI CannonMainI.
From CRIS.cannon Require Import CannonA CannonMainA.
From CRIS.cannon Require Import CannonIAproof CannonMainIAproof.

Section CannonAux.
  Import CannonA.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _CANNON: !cannonGS}.
  Local Definition smod_src : SMod.t := CannonA.smod ☆ (MainA.smod 1).
  Local Definition mod_top : Mod.t := (SMod.to_mod ∅ (SMod.cancel smod_src)).
  Local Definition mod_tgt : Mod.t := CannonI.t ★ (MainI.t 1).
  
  Local Definition sp : specmap := SMod.sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Lemma cancel_src :
    Ball ∗ Cancel.init_res ⊢ refines mod_src mod_top.
  Proof.
    iIntros "[H1 H2]".
    iApply refines_trans. iSplitR.
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { apply SMod.cancellable_add; r; rewrite /=; mod_tac ss. }
    { ss. exists tt. split; refl. }
    { unfoldPrePost. iIntros "% % %"; by des. }
    { iDestruct "H2" as "(X & Y & Z & $ & $)".
      unfoldPrePost. iSplit; et.
    }
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt :
    Ready ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "H".
    iApply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src SMod.to_mod_add.
    iApply ctxr_compose_hor. iSplitL.
    - iApply CannonIA.ctxr; et.
    - iApply CannonMainIA.ctxr.
      split; et.
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq.
      mod_tac.
  (*SLOW*)Qed.

  Lemma top_tgt :
    Ready ∗ Ball ∗ Cancel.init_res ⊢ refines mod_tgt mod_top.
  Proof.
    iIntros "(H1 & H2 & H3)".
    iApply refines_trans. iSplitL "H1".
    - iApply src_tgt; iFrame.
    - iApply cancel_src; iFrame.
  Qed.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    eapply Mod.add_wf.
    { econs; eauto; [mod_tac|prove_nodup]. }
    { econs; eauto; [mod_tac|prove_nodup]. }
    { mod_tac. }
    { prove_nodup; set_solver. }
  Qed.
End CannonAux.

Module CannonAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; concΓ; cannonΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : cannonGS) src_res,
      ✓ src_res
      /\ refines_lmod
          (Mod.to_lmod mod_tgt ε)
          (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV H0])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINV∅]".
    iMod cannon_alloc as "(% & H1 & H2)".
    iExists _, _, _, _, _.
    iPoseProof (top_tgt with "[WINV H0 H1 H2]") as "REF".
    { iFrame. iDestruct "H0" as "(H0 & H1 & H2 & H3)". iFrame. }
    iApply refines_adequacy. { eapply tgt_wf. }
    iFrame; et.
  Qed.

End CannonAll.
(* Print Assumptions CannonAll.behavioral_refinement. *)
