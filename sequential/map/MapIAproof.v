From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA.
From CRIS.map Require Export MapHeader MapA MapM MapI MapIMproof MapMAproof.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS, _MAP: !mapGS, _MEM: !memGS}.

  Lemma ctxr (sp_s sp_mem : specmap)
      (MapInSpMap : MapA.sp ⊆ sp_s) :
    MapA.init_cond ⊢
      ctx_refines
        (MapI.t ★ MemA.t sp_mem)
        (MapA.t sp_s ★ MemA.t sp_mem).
  Proof.
    iIntros "H". iApply ctxr_trans. iSplitR "H".
    { iApply MapIM.ctxr. instantiate (1 := MapM.sp); refl. }
    iApply ctxr_frameR. iApply MapMA.ctxr; eauto.
  Qed.
End MapIA. End MapIA.
