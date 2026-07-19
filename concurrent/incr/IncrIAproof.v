Require Import CRIS.common.CRIS CRIS.scheduler.Atomic.
From CRIS.scheduler Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA MemTactics.
Require Import IncrHeader IncrI IncrA.

Module IncrIA. Section IncrIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !concGS}.
  Context (sp_m : specmap).

  Local Definition IstFull := (IstProd (IstSB [] IstTrue) IstEq).
  Local Notation MA := (IncrA.t ★ MemA.t sp_m).
  Local Notation MI := (IncrI.t ★ MemA.t sp_m).

  Lemma incr_simF : ISim.sim_fun open MA MI IstFull (fid IncrHdr.incr).
  Proof.
    cStartFunSim. rewrite /IncrA.incr /IncrI.incr. cStepsS. cStepsT.
    aStepS (N [blk ofs]) "->". cStepsT. aAddY. sYields.

    iApply wsim_reset. cCoind CIH g __ with st_src st_tgt. iIntros "? /=".
    aUnfoldT. sYields. sYieldS. aUnfoldS. sYieldS. cStepsS.
    rename _q into v; iRename "ASM" into "↦".
    mLoad. cForceS (inl tt); cForcesS; iFrame "↦". cStepsS.

    aUnfoldS. sYields. sYieldS. cStepsS. rename _q into v2; iRename "ASM" into "↦".
    mCas. instantiate (1:=emp%I). iSplitR; first done. iSplitR.
    { iIntros "_"; iExists 1%Qp, 1%Qp, Vundef, Vundef; ss. }
    iIntros "↦ _". cStepsT. case_bool_decide.
    { case_bool_decide; subst; ss. cForceS (inr _); cForcesS; iFrame "↦".
      sYields. rewrite decide_True //. cStepsT. sYieldS. cStep; iFrame; iModIntro; iSplit; ss.
    }
    case_bool_decide; ss. cForceS (inl tt). cForcesS; iFrame. cStepsS.
    aAddY. sYields. case_decide; ss. cStepsT. sYieldS. aAddY.
    cByCoind CIH. iFrame.
  Qed.
End IncrIA. End IncrIA.
