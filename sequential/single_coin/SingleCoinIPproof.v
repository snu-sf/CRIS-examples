From CRIS.common Require Import CRIS.
From CRIS.simulations.filter Require Import CallFilter.
Require Export SingleCoinHeader SingleCoinI SingleCoinP.
From CRIS.prophecy Require Export ProphecyHeader ProphecyI.

Module SingleCoinIP. Section SingleCoinIP.
  Import SingleCoinP SingleCoinI.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context (mn : string).

  Local Notation MA := (SingleCoinP.t mn ★ ProphecyI.t mn).
  Local Notation MI := (CFilter.filter (Prophecy.exports mn) SingleCoinI.t ★ ProphecyI.t mn).

  Local Definition Ist : ist_type Σ :=
    (λ st_s st_t,
      ∃ (l : list (option bool)), ⌜st_s = {[v_coins # l↑]} ∧ st_t = st_s⌝)%I.

  Local Definition IstFull := IstProd (IstSB (Mod.scopes (SingleCoinP.t mn)) Ist) IstEq.

  Lemma simF_new : ISim.sim_fun open MA MI IstFull (fid SingleCoinHdr.new).
  Proof.
    cStartFunSim. rewrite /SingleCoinI.new /SingleCoinP.new.
    iDestruct "IST" as "%"; des; subst.
    cStepsS. cStepsT. destruct Any.downcast; cStepsS; last case_match; cStepsS; ss.
    cStepsT. cInlineS. rewrite /ProphecyI.new. cStepsS. cStep.
    iSplit; eauto. do 4 iExists _. iSplit; eauto.
    do 2 (iSplit; eauto; ss).
  Qed.

  Lemma simF_read : ISim.sim_fun open MA MI IstFull (fid SingleCoinHdr.read).
  Proof.
    cStartFunSim. rewrite /SingleCoinI.read /SingleCoinP.read.
    iDestruct "IST" as "%"; des; subst.
    cStepsS. cStepsT. destruct (Any.downcast arg); cStepsS; last case_match; cStepsS; ss.
    cStepsT. des_ifs.
    { cStep; eauto. iSplit; eauto.
      do 4 iExists _. iSplit; eauto; cycle 1.
      do 2 (iSplit; eauto; ss).
    }
    { cStepsT. cForceS. cStepsS. rewrite /v_coins /SingleCoinP.v_coins.
      cInlineS. rewrite /ProphecyI.new. cStepsS. cStep. iSplit; eauto.
      do 4 iExists _. iSplit; eauto.
      do 2 (iSplit; eauto; ss).
    }
    { rewrite /triggerUB. cStepsS. des_ifs; cStepsS; ss. }
  Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    cStartModSim.
    { eapply simF_new; eauto. }
    { eapply simF_read; eauto. }
    { iPureIntro; esplits; ss. }
  Qed.
End SingleCoinIP. End SingleCoinIP.
