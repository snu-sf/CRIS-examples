Require Import CRIS Atomic.
Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA MemTactics.
Require Import IncrHeader IncrI IncrA.

Module IncrIA. Section IncrIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !concGS, !schGS}.
  Context (sp : specmap).

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (IncrA.t)) IstTrue) IstEq).
  Local Notation MA := (IncrA.t ★ (MemA.t sp)).
  Local Notation MI := (IncrI.t ★ (MemA.t sp)).

  Lemma incr_simF : ISim.sim_fun open MA MI IstFull (fid IncrHdr.incr).
  Proof.
    cStartFunSim. cStepsS. cStepsT. iApply atomic_fun_src.
    iIntros ([blk ofs]) "->". rewrite /IncrI.incr unfold_atomic_update. cStepsT. cStepsS.

    sYieldRR "IST". sYieldRR "IST".

    iApply wsim_reset.
    cCoind CIH g __ with st_src st_tgt.
    iIntros "IST /=".

    unfoldIterCT. cStepsT. sYieldRR "IST". sYieldS. cStepsS.
    rename _q into v; iRename "ASM" into "↦".
    mLoadT "↦". cForceS (inl tt); cForcesS; iFrame "↦". cStepsS.
    rewrite unfold_atomic_update; cStepsS. sYieldRR "IST". sYieldRR "IST". sYieldS; cStepsS.
    rename _q into v2; iRename "ASM" into "↦".

    iApply (wsim_mem_cas with "↦"); [prove_inline_cond|ss|eauto| | | ].
    { rewrite /MemA.compare_val; des_ifs. }
    { instantiate (1:=emp%I); done. }
    { iIntros "_"; iExists 1%Qp, 1%Qp, Vundef, Vundef; ss. }
    iIntros "↦ _". cStepsT. case_bool_decide.
    { case_bool_decide; subst; ss. cForceS (inr _); cForcesS; iFrame "↦".
      cStepsS. sYieldRR "IST". sYieldRR "IST".
      rewrite decide_True //. cStepsT. sYieldS. cStep; iFrame; iSplit; first ss.
      cStep. iFrame. done.
    }
    case_bool_decide; ss. cForceS (inl tt). cForcesS; iFrame. cStepsS.
    rewrite unfold_atomic_update; cStepsS.
    sYieldRR "IST". sYieldRR "IST". case_decide; ss. cStepsT.
    cByCoind CIH. iFrame.
  (*SLOW*)Qed.
End IncrIA. End IncrIA.
