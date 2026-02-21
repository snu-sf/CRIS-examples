Require Import CRIS SystemHeader SystemA.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I, _SYS: !sysGS}.

  Lemma wsim_system_yield_ir
      fl_src fl_tgt Ist r g R_src R_tgt RR p_src p_tgt
      st_src st_tgt itr_src itr_tgt
      (tid : Ident.t) (stid : nat) (V : TView.t)
      (E : coPset)
      (msk_src msk_tgt : emask)
      sp_src sp_tgt :
    sp_src.1 !! fid SystemHdr.yield = fsp_some (SystemA.yield_spec E) →
    sp_tgt.1 !! fid SystemHdr.yield = None →
    (∀ X, msk_tgt _ (subevent _ (Choose X))) →
    (msk_tgt _ (subevent _ (Call SystemHdr.yield ()↑))) →
    Ist st_src st_tgt ∗
    (tview_sys tid stid V) ∗
    (∀ st_src st_tgt,
      Ist st_src st_tgt -∗
      (tview_sys tid stid V) -∗
      wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR true true
        (st_src, SB.sandbox msk_src (SModTr.trans sp_src 𝒴) >>= itr_src)
        (st_tgt, itr_tgt ())) ⊢
    wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR p_src p_tgt
      (st_src, SB.sandbox msk_src (SModTr.trans sp_src 𝒴) >>= itr_src)
      (st_tgt, SB.sandbox msk_tgt (SModTr.trans sp_tgt 𝒴) >>= itr_tgt).
  Proof.
    intros Hsps Hspt Hmsk Hcall.
    rewrite /System.yield; unseal "System".
    revert p_src. combine_quant p_tgt.
    combine_quant st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' Hgg' CIH [st_tgt [st_src [p_src p_tgt]]]) "[IST [TV KTR]] /=".
    destruct_quant CIH.

    unfold_iterC_r.
    steps_r. rewrite Hmsk. steps_r. destruct _q as [[|]|]; cycle 2.
    { steps_r.
      unfold_iterC_l.
      steps_l. des_ifs; step_l; ss.
      force_l (Some false). steps_l.
      iApply wsim_mono_knowledge; cycle 2.
      { iApply ("KTR" with "IST TV"). }
      { ii; iIntros "$ !> //". }
      { ii; iIntros "G"; iPoseProof (Hgg' with "G") as "$"; done. }
    }
    { steps_r. rewrite Hspt. steps_r. rewrite Hcall. steps_r.
      unfold_iterC_l. steps_l. des_ifs; step_l; ss.
      force_l (Some true). steps_l. rewrite Hsps /=.
      step_l. des_if; step_l; ss. force_l (tid, stid, V).
      step_l. des_if; step_l; ss. force_l.
      step_l. des_if; step_l; ss. force_l.
      iFrame "TV". iSplit; eauto.
      step_l. des_if; step_l; ss.
      call "IST".
      clear st_src st_tgt. iIntros (ret st_src st_tgt) "IST".
      step_l. des_if; step_l; ss.
      step_l. des_if; steps_l; ss. steps_r.
      by_coind CIH. iFrame. iDestruct "ASM" as "[? [? $]]".
    }
    unfold_iterC_l.
    steps_l. des_if; step_l; ss. force_l (Some false). steps_l. steps_r.
    by_coind CIH. iFrame.
  (*SLOW*)Qed.

  Lemma wsim_system_yield_src
      fl_src fl_tgt Ist r g R_src R_tgt RR p_src p_tgt
      st_src st_tgt itr_src itr_tgt
      (E : coPset)
      (msk_src : emask)
      sp_src :
    wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR true p_tgt
      (st_src, itr_src ())
      (st_tgt, itr_tgt) ⊢
    wsim fl_src fl_tgt Ist (E, E) r g R_src R_tgt RR p_src p_tgt
      (st_src, SB.sandbox msk_src (SModTr.trans sp_src 𝒴) >>= itr_src)
      (st_tgt, itr_tgt).
  Proof.
    iIntros "S"; rewrite /System.yield; unseal "System".
    unfold_iterC_l; steps_l.
    des_if; steps_l; ss. force_l (None); steps_l; done.
  Qed.
End wsim.
