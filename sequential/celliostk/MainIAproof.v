From CRIS.common Require Import CRIS.
From CRIS.imp_system Require Import mem.MemA.
From CRIS.celliostk Require Import CellioHeader CellioA MainHeader MainA MainI CtxHeader.

Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Context (sp : specmap).
  Context (sp_foo: sp.1 !! fid CtxHdr.foo = None).
  Context (sp_cb: sp.1 !! fid MainHdr.input_cb = None).
  
  Local Definition CellioAMod := (CellioA.t).
  Local Definition MainA := (MainA.t sp).
  Local Definition IstFull := (IstProd (IstSB MainA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_cb : ISim.sim_fun open MainA (MainI.t ★ CellioAMod) IstFull (fid MainHdr.input_cb).
  Proof using.
    cStartFunSim. unfold MainA.input_cb, MainI.input_cb.
    destruct Any.downcast; cStepsS; des_ifs.
    cStepsS. cStepsT. cStep. cStep. cStep. iSplit; et.
  Qed. 

  Lemma simF_main : ISim.sim_fun open MainA (MainI.t ★ CellioAMod) IstFull entry.
  Proof using sp_foo sp_cb.
    cStartFunSim. unfold MainA.main, MainI.main.
    
    cStepsS. cStepsT.

    cInlineT. cStepsT. iDestruct "GRT" as "->".
    cStep. cStepsS. cStepsT. rename ret into i.

    cBind (λ '(sts,ls) '(stt,stk), IstFull sts stt ∗ ll_points_to stk ls)%I "IST"
      as (st_src ? st_tgt ?) "[IST PT]".
    {
      destruct (Z.le_dec 0 i); cycle 1.
      { rewrite !unfold_iter. case_match; try nia.
        cStepsS. cStepsT. cStep. et.
      }
      eapply Z_of_nat_complete in l. des; subst.
      iAssert (ll_points_to Vnullptr []) as "PT"; et.
      iRevert "PT". rewrite bi.intuitionistically_elim. iIntros "PT".
      generalize ([]: list Z) as ls, Vnullptr as stk. i.
      iStopProof. revert ls stk st_src st_tgt. induction n; i; iIntros "[IST PT]".
      { rewrite !unfold_iter. cStepsS. cStepsT. cStep. et. }
      rewrite !unfold_iter. cStepsT. cStepsS. cSimpl.

      cInlineT. cStepsT. cForceT ls. cStepsT. cForceT. iSplitL "PT"; et. cStepsT. cSimpl.
      cCall "IST" as (ret ? ?) "IST".
      cStepsS. cStepsT. destruct Any.downcast; [|cStepsS; ss].
      cStepsS. cStepsT. iDestruct "GRT" as (??) "[-> [PH PT]]".
      replace (S n - 1)%Z with (n: Z) by nia.
      rewrite -IHn. iFrame. et.
    }

    cStepsT. cStepsS. cSimpl. cCall "IST" as (? ? ?) "IST". cStepsS. cStepsT.
    destruct Any.downcast; [|cStepsS; ss]. cStepsS. cStepsT.
    iStopProof. clear_st. revert r_t st_s' st_t'. induction r_s; i; iIntros "[PT IST]".
    { rewrite !unfold_iter. cStepsS. cStepsT. cInlineT. cStepsT.
      cForceT []. cStepsT. cForceT. iFrame. cStepsT. cStep. iFrame. et. }
    rewrite !unfold_iter. cStepsS. cStepsT.
    cInlineT. cStepsT. cForceT (a::r_s). cStepsT. cForceT. iFrame.
    cStepsT. cStep. cStepsS. cStepsT.
    rewrite -IHr_s. iFrame.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MainA (MainI.t ★ CellioAMod) emp IstFull.
  Proof using sp_foo sp_cb.
    cStartModSim.
    { iIntros "_". unfold IstFull, IstProd. repeat (iExists ∅). ss. }
    { eapply simF_cb; eauto. }  
    { eapply simF_main; eauto. }
  Qed.
End MainIA. End MainIA.
