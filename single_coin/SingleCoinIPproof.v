Require Import CRIS CallFilter.
Require Export SingleCoinHeader SingleCoinI SingleCoinP.
Require Export ProphecyHeader ProphecyI.

Module SingleCoinIP. Section SingleCoinIP.
  Import SingleCoinP SingleCoinI.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context (mn : string).

  Local Notation MA := (SingleCoinP.t mn ★ ProphecyI.t mn).
  Local Notation MI := (CFilter.filter (ProphecyName.exports mn) SingleCoinI.t ★ ProphecyI.t mn).

  Local Definition Ist : ist_type Σ :=
    (λ st_s st_t,
      ∃ (l : list (option bool)), ⌜st_s = {[v_coins # l↑]} ∧ st_t = st_s⌝)%I.

  Local Definition IstFull := IstProd (IstSB (Mod.scopes (SingleCoinP.t mn)) Ist) IstEq.

  Lemma simF_new : ISim.sim_fun open MA MI IstFull (fid SingleCoinHdr.new).
  Proof.
    iStartSim. rewrite /SingleCoinI.new /SingleCoinP.new.
    iDestruct "IST" as "%"; des; subst.
    steps_l. steps_r. destruct Any.downcast; steps_l; last case_match; steps_l; ss.
    steps_r. inline_l. rewrite /ProphecyI.new. steps_l. step.
    iSplit; eauto. do 4 iExists _. iSplit; eauto.
    do 2 (iSplit; eauto; ss).
  Qed.

  Lemma simF_read : ISim.sim_fun open MA MI IstFull (fid SingleCoinHdr.read).
  Proof.
    iStartSim. rewrite /SingleCoinI.read /SingleCoinP.read.
    iDestruct "IST" as "%"; des; subst.
    steps_l. steps_r. destruct (Any.downcast arg); steps_l; last case_match; steps_l; ss.
    steps_r. des_ifs.
    { step; eauto. iSplit; eauto.
      do 4 iExists _. iSplit; eauto; cycle 1.
      do 2 (iSplit; eauto; ss).
    }
    { steps_r. force_l. steps_l. rewrite /v_coins /SingleCoinP.v_coins.
      inline_l. rewrite /ProphecyI.new. steps_l. step. iSplit; eauto.
      do 4 iExists _. iSplit; eauto.
      do 2 (iSplit; eauto; ss).
    }
    { rewrite /triggerUB. steps_l. des_ifs; steps_l; ss. }
  Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { eapply simF_new; eauto. }
    { eapply simF_read; eauto. }
    { iPureIntro; esplits; ss. }
  Qed.
End SingleCoinIP. End SingleCoinIP.
