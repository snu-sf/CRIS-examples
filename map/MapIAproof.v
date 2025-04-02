Require Import CRIS.

Require Import MapHeader MapA MapM MapI ModSim MapIMproof MapMAproof MemA.

Module MapIA. Section MapIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.

  Lemma ctxr (sp_s sp_mem : string → option fspec)
      (MapInSpMap : sp_incl MapAS.sp sp_s) :
    ctx_refines
      ((MapA.t sp_s) ★ (MemA.t sp_mem), (MapA.init_cond ∗ MapM.init_cond)%I)
      ((MapI.t)           ★ (MemA.t sp_mem), emp%I).
  Proof.
    etrans; cycle 1.
    { eapply MapIM.ctxr.
      instantiate (1:= to_sp MapMS.sp).
      i. split; try refl. unfold MapMS.sp. unseal CRIS. prove_nodup.
    }
    eapply ctxr_frameR. rewrite -(hmod_addc_empty_l (MapM.t _)). eapply ctxr_cond_frameR.
    eapply MapMA.ctxr; eauto. rewrite /MapMS.sp; unseal CRIS; prove_nodup. ss.
  Qed.
End MapIA. End MapIA.
