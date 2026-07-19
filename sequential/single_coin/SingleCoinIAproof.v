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
    refines
      (CoinI ★ md, emp%I)
      (CoinA ★ md, ProphecyA.initial_cond ∗ SingleCoinA.init_cond)%I.
  Proof.
    intros Hreal.
    etrans.
    { eapply prophecy_main with (Pm:=emp%I); eauto.
      { intros mn; eapply main_adequacy, SingleCoinIP.sim. }
      { intros mn; eapply main_adequacy, SingleCoinPA.sim. }
      { intros mn. rewrite /real_mod.
        mod_tac (s; esplits; ii; edestruct excluded_middle_informative; ss).
      }
    }
    eapply ctxr_refines, ctxr_consequence; iIntros "[$ $] //".
  Unshelve. all: apply True.
  Qed.
End SingleCoinIA. End SingleCoinIA.
