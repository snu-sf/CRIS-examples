Require Import CRIS.common.CRIS CRIS.scheduler.Atomic.
From CRIS.scheduler Require Import SchHeader SchA SchTactics.
From CRIS.imp_system Require Import imp.ImpPrelude mem.MemHeader mem.MemA.
From CRIS.imp_system Require Import mem.MemTactics.
From CRIS.incr Require Import IncrHeader IncrI IncrA.

Module IncrIA. Section IncrIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !concGS}.
  Context (sp_m : specmap).

  Local Notation MA := (IncrA.t ★ MemA.t sp_m).
  Local Notation MI := (IncrI.t ★ MemA.t sp_m).
  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Local Definition IstFull : iProp Σ :=
    (True ∗ IstEq (MemA.t sp_m))%I.

  Lemma incr_simF :
    ⊢ ISim.sim_fun open MA MI IstFull (fid IncrHdr.incr).
  Proof.
    cStartFunSim. rewrite /IncrA.incr /IncrI.incr. cStepsS. cStepsT.
    aStepS (N [blk ofs]) "->". cStepsT. aAddY. sYields.

    iApply wsim_reset. cCoind CIH g __ with blk ofs. iIntros "? /=".
    aUnfoldT. sYields. sYieldS. aUnfoldS. sYieldS. cStepsS.
    rename _q into v; iRename "ASM" into "↦".
    mLoad. cForceS (inl tt); cForcesS; iFrame "↦". cStepsS.

    aUnfoldS. sYields. sYieldS. cStepsS. rename _q into v2; iRename "ASM" into "↦".
    mCas. instantiate (1:=emp%I). iSplitR; first done. iSplitR.
    { iIntros "_"; iExists 1%Qp, 1%Qp, Vundef, Vundef; ss. }
    iIntros "↦ _". cStepsT. case_bool_decide.
    { case_bool_decide; subst; ss. cForceS (inr _); cForcesS; iFrame "↦".
      sYields. rewrite decide_True //. cStepsT. sYieldS.
      cStepsS. iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
      iFrame. iModIntro. iSplit; ss.
    }
    case_bool_decide; ss. cForceS (inl tt). cForcesS; iFrame. cStepsS.
    aAddY. sYields. case_decide; ss. cStepsT. sYieldS. aAddY.
    cByCoind CIH. iFrame.
  Qed.

  End SIM_FUNS.


End IncrIA. End IncrIA.
