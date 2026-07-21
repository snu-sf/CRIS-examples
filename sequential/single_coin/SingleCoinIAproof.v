From CRIS.common Require Import CRIS.
From CRIS.single_coin Require Import SingleCoinIPproof SingleCoinPAproof.
From CRIS.prophecy Require Import ProphecyFacts.

Module SingleCoinIA. Section SingleCoinIA.
  Context `{!crisG Γ Σ α β τ _S _I, !prophGS, !coinGS}.
  Context (sp : specmap).

  Local Notation CoinI := (SingleCoinI.t).
  Local Notation CoinA := (SingleCoinA.t sp).

  Lemma ctxr (md : Mod.t) :
    real_mod md →
    ProphecyA.initial_cond ∗ SingleCoinA.init_cond ⊢
      refines (CoinI ★ md) (CoinA ★ md).
  Proof.
    intros Hreal.
    iIntros "[HP HC]".
    iApply (prophecy_main CoinA CoinI md SingleCoinP.t).
    { intros mn. rewrite /real_mod.
      mod_tac (s; esplits; ii; edestruct excluded_middle_informative; ss).
    }
    { exact Hreal. }
    iSplitR "HP HC".
    { iIntros (mn). iApply main_adequacy.
      { eapply SingleCoinIP.sim. }
      iEmpIntro.
    }
    iFrame "HP".
    iIntros (mn). iApply main_adequacy.
    { eapply SingleCoinPA.sim. }
    iFrame.
    Unshelve. all: apply True.
  Qed.
End SingleCoinIA. End SingleCoinIA.
