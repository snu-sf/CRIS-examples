Require Import CRIS.
Require Import SchTactics MemTactics.
Require Export FaaHeader FaaI FaaA.

Module FaaIA. Section FaaIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS}.
  Context (sp : specmap).

  Local Definition IstFull := (IstProd (IstSB FaaA.t.(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (FaaA.t ★ MemA.t sp).
  Local Definition MI := (FaaI.t ★ MemA.t sp).

  Lemma faa2_simF : ISim.sim_fun open MA MI IstFull (fid FaaHdr.faa2).
  Proof using.
    cStartFunSim. rewrite /FaaI.faa2 /FaaA.faa2.

    cStepsS.
    destruct (arg ↓) as [[|v [|v' l]]|]; cStepsS; ss.
    destruct v as [|[blk ofs]|]; cStepS; ss.

    cStepsT. sYieldRR "IST". cStepsT.
    rewrite /MemHdr.faa; cStepsT.

    sYieldS; cStepsS. rename _q into v.
    mLoadT "ASM". mStoreT "ASM". cForceS; iFrame "ASM". cStepsS.
    sYieldRR "IST".

    sYieldS; cStepsS. clear v. rename _q into v.
    mLoadT "ASM". mStoreT "ASM".
    cForceS; iFrame "ASM".
    sYieldRR "IST". sYieldS. cStep. iFrame; done.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    cStartModSim.
    { eapply faa2_simF. }
    { iIntros "_"; iExists _, _, _, _; iSplit; eauto. }
  Qed.
End FaaIA. End FaaIA.
