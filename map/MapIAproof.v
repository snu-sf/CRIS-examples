Require Import CRIS.

Require Import MapHeader MapA MapM MapI ModSim MapIMproof MapMAproof MemA.

Module MapIA. Section MapIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.

  Lemma ctxr (u_s u_mem : univ_id) (sp_s sp_mem : string → option fspec)
      (LE : u_s >= 2)
      (MapInSpMap : sp_incl (MapAS.sp u_s) sp_s) :
    ctx_refines
      ((MapA.t u_s sp_s) ★ (MemA.t u_mem sp_mem), (MapA.init_cond ∗ MapM.init_cond)%I)
      ((MapI.t)           ★ (MemA.t u_mem sp_mem), emp%I).
  Proof.
    etrans; cycle 1.
    { eapply MapIM.ctxr.
      instantiate (1:= to_sp (MapMS.sp 1)).
      i. split; try refl. unfold MapMS.sp. unseal CRIS. prove_nodup.
    }
    eapply ctxr_frameR. rewrite -(hmod_addc_empty_l (MapM.t _ _)). eapply ctxr_cond_frameR.
    eapply MapMA.ctxr; eauto. rewrite /MapMS.sp; unseal CRIS; prove_nodup. ss.
  Qed.
End MapIA. End MapIA.