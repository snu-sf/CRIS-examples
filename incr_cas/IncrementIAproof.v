Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA MemTactics.
Require Import IncrementHeader IncrementI IncrementA.

Module IncrementIA. Section IncrementIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS}.
  Context (sp : specmap).

  Local Definition IstFull := (IstProd (IstSB IncrementA.t.(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (IncrementA.t ★ (MemA.t sp)).
  Local Definition MI := (IncrementI.t ★ (MemA.t sp)).

  Lemma increment_simF : ISim.sim_fun open MA MI IstFull (fid IncrementHdr.increment).
  Proof.
    cStartFunSim. rewrite /IncrementI.increment /IncrementA.increment.
    cStepsT. cStepsS.
    destruct (arg ↓) as [[|v [|v' l]]|]; cStepS; ss.
    destruct v as [|[blk ofs]|]; cStepS; ss. cStepsT.

    sYieldRR "IST". sYieldRR "IST".
    sYieldS. cStepsS.

    iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt. iIntros "IST /=".
    unfoldIterCT. cStepsT.
    unfoldIterCS. cStepsS.
    sYieldRR "IST".

    sYieldS. cStepsS. rename _q into v.

    mLoadT "ASM". cForceS false. cStepsS. cForceS; iFrame "ASM". cStepsS. sYieldS. cStepsS.
    unfoldIterCS. cStepsS.

    sYieldRR "IST". sYieldRR "IST".

    sYieldS. cStepsS. rename _q into v'.
    iApply (wsim_mem_cas with "ASM"); [prove_inline_cond|ss|eauto| | | ].
    { rewrite /MemA.compare_val; des_ifs. }
    { instantiate (1:=emp%I); done. }
    { iIntros "_"; iExists 1%Qp, 1%Qp, Vundef, Vundef; ss. }
    iIntros "↦ _".

    cStepsT.
    repeat case_bool_decide; subst; ss.
    { cForceS true. cStepsS. cForceS; iFrame "↦"; cStepsS.
      sYieldRR "IST". sYieldRR "IST".
      case_decide; [|ss].
      cStepsT.
      sYieldS. cStepsS. cStep. iSplit; done.
    }
    { cForceS false.
      cForcesS. iFrame "↦". cStepsS.
      sYieldRR "IST". sYieldRR "IST".
      case_decide; first clarify.
      cStepsT.
      sYieldS. cStepsS.
      iApply wsim_progress. iApply wsim_base.
      iIntros "?". iApply (CIH). iFrame.
    }
  (*SLOW*)Qed.
End IncrementIA. End IncrementIA.
