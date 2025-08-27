Require Import CRIS MemA.

From CRIS.map Require Import Header MapA MapM MapI MapIMproof MapMAproof.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{!mapMG}.
  Context `{!mapG}.
  Context `{!memG}.

  Lemma ctxr (sp_s : string → option fspec)
      (MapInSpMap : sp_incl MapAS.sp sp_s) :
    ctx_refines
      ((MapA.t sp_s) ★ (MemP.t), (MapA.init_cond ∗ MapM.init_cond)%I)
      ((MapI.t)      ★ (MemP.t), emp%I).
  Proof.
    etrans; cycle 1.
    { eapply MapIM.ctxr.
      instantiate (1:= to_sp MapMS.sp).
      i. split; try refl. unfold MapMS.sp. unseal CRIS. prove_nodup.
      i. unfold to_sp, MapMS.sp in *; rewrite H2; ss.
    }
    eapply ctxr_frameR. rewrite (mod_addc_empty_l (MapM.t _)). eapply ctxr_cond_frameR.
    eapply MapMA.ctxr; eauto. unfold MapMS.sp. unseal CRIS. prove_nodup.
    i. unfold to_sp, MapMS.sp in *; rewrite H2; ss.
  Qed.
End MapIA. End MapIA.
