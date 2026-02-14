Require Import CRIS MemA.
Require Export MapHeader MapA MapM MapI MapIMproof MapMAproof.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS, _MAP: !mapGS, _MEM: !memGS}.

  Lemma ctxr (sp_s sp_mem : specmap)
      (MapInSpMap : MapA.sp ⊆ sp_s) :
    ctx_refines
      (MapA.t sp_s ★ MemA.t sp_mem, MapA.init_cond)
      (MapI.t      ★ MemA.t sp_mem, emp%I).
  Proof.
    etrans; cycle 1.
    { eapply MapIM.ctxr. instantiate (1:= MapM.sp); refl. }
    eapply ctxr_frameR.
    eapply MapMA.ctxr; eauto.
  Qed.
End MapIA. End MapIA.
