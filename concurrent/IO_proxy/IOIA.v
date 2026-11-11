Require Import CRIS.common.CRIS.
From CRIS.filter Require Import CallFilter.
From CRIS.proofmode Require Import BiEnrichedProset.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.IO_proxy Require Import IOHeader IOI IOA.
From CRIS.imp_system Require Import mem.MemHeader.
Require Import CRIS.scheduler.SchHeader.
From CRIS.priority_queue Require Import PQueueHeader.
From CRIS.IO_proxy Require Import IOHeader.
From CRIS.scheduler Require Import Atomic SchA SchTactics.
From CRIS.priority_queue Require Import PQueueA.
From CRIS.elimination_stack Require Import StackA.
From CRIS.imp_system Require Import mem.MemA.
From CRIS.imp_system Require Import mem.MemTactics.
From CRIS.helping Require Import HelpingTactics HelpingFacts.
Require Import CRIS.scheduler.SchI.

(* Helper lemma: prepend a 𝒴@{N} to ITree.iter whose body starts with 𝒴@{N}.
   Same idea as yield_iter_prepend_yield_src but for the form induced by
   wsim_helping_help (plain ITree.iter without the trailing 𝒴+Ret). *)
Lemma helping_iter_prepend_yield_src `{!crisG Γ Σ α β τ Hinv Hsub}
    `{STATE : !stateGS Σ}
    (N : option namespace)
    {I R : Type} (body : I → itree crisE (I + R)) (arg : I)
    (fl_s fl_t : gmap fname (Any.t → itree crisE Any.t))
    (Ist : iProp Σ)
    (ps pt : bool)
    (Es : coPset) g
    {R_s R_t} (RR : retr_type Σ R_s R_t)
    (msk_s : emask)
    (sp_s : specmap)
    (ktr_s : R → itree crisE R_s)
    (itr_t : itree crisE R_t) :
  wsim fl_s fl_t Ist (Es, Es) g _ R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{N});;;
      ⇓sbox(msk_s) (⇓smod(sp_s) (ITree.iter (λ a : I, 𝒴@{N};;; body a) arg)) >>= ktr_s)
    itr_t ⊢
  wsim fl_s fl_t Ist (Es, Es) g _ R_t RR ps pt
    (⇓sbox(msk_s) (⇓smod(sp_s) (ITree.iter (λ a : I, 𝒴@{N};;; body a) arg)) >>= ktr_s)
    itr_t.
Proof.
  iIntros "SIM". rewrite unfold_iter. cNormS. iApply wsim_yy_y_namespace.
  eapply eq_ind; first iApply "SIM".
  repeat f_equal; extensionalities; etrans; first hnorm_itr; auto.
Qed.

Module IOIM. Section IOIM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.
  Context (mn : string).
  Context (sp_user : specmap).

  Local Notation IOI := (CFilter.filter (Helping.exports mn) (IOI.t)).
  Local Notation ProxyI := (CFilter.filter (Helping.exports mn) (ProxyI.t)).
  Local Notation Mem := (CFilter.filter (Helping.exports mn) (MemA.t ∅)).
  Local Notation PQ := (CFilter.filter (Helping.exports mn) (PQueueA.t)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation IOHelpM := ((IOM.t mn ★ ProxyM.t mn) ★ HelpingOn.t mn jobCode).
  Local Notation IOHelpI := ((IOI ★ ProxyI) ★ HelpingDummy.t mn).
  Local Notation Ctx := ((PQ ★ Mem) ★ SchI).
  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Local Definition IstFull : iProp Σ :=
    (IstHelp (IstEq IOHelpM) ⊤ ∗ IstEq Ctx)%I.

  Lemma init_simF : ⊢ ISim.sim_fun open
    (IOHelpM ★ Ctx)
    (IOHelpI ★ Ctx)
    IstFull (fid IOHdr.init).
  Proof.
    cStartFunSim. rewrite /IOA.init /IOI.init. cStepsS.
    aStepS (N sz) "[-> %Hsz]". cStepsT. cNormS. sYields.
    cInlineT. rewrite /PQueueA.new. cStepsT.
    aForceT (N.@"queue") with ""; first (instantiate (1:=(_, _))); ss.
    sYields. destruct _q as [ret _]. cStepsT.
    iDestruct "GRT" as "[%q [%γq [-> [#Hq Q]]]]". cStepsT. sYields. sYieldS.
    iMod (inv_alloc (syn_proxy_inv N γq sz) 1 _ _ (N.@"proxy") with "[Q]") as "#Hproxy"; auto.
    { solve_ndisj. }
    { rewrite sl_red; iFrame "Q".
      rewrite length_replicate; iSplitR; first done.
      generalize sz at 2; intros ?;
        iInduction sz as [|sz]; [ss|iSplitR; [ss|iApply "IHsz"; iPureIntro; lia]].
    }
    iAssert (is_proxy N q sz)%I as "#proxy".
    { iFrame "#". iDestruct "Hq" as "[% [% [-> [% [% [? ?]]]]]]"; iFrame "#"; eauto. }

    cForceS q. iApply (wsim_spawn_f_src _ _ _ (λ _ _, existT 0 ⌜False⌝)%SAT with "IST []"); ss.
    { case_bool_decide as Hcase; ss. set_solver+Hcase. }
    { iIntros (mtid stid) "W T"; iExists (stid, mtid, tt); unfoldPrePost.
      iSplitL; [iFrame "∗#"; eauto|].
      iIntros "%% [? [? []]]".
    }
    iIntros (tid) "IST J". cStepsS. cStepsT.
    iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
    iFrame "∗#"; eauto.
  Qed.

  Lemma request_simF : ⊢ ISim.sim_fun open
    (IOHelpM ★ Ctx)
    (IOHelpI ★ Ctx)
    IstFull (fid IOHdr.request).
  Proof.
    cStartFunSim. rewrite /IOM.request /IOI.request. cStepsS.
    aStepS (N [[[q [cb cofs]] num] prt]) "[-> [%sz [[%qb [%qofs [-> [%γq [#queue #proxy]]]]] %Hsz]]]".
    cStepsS; cStepsT.
    iApply wsim_helping_run; [prove_inline_cond|].
    iIntros (reqid) "help". sYields.
    mAllocT as (hb) "/= [hb1 [hb2 [hb3 _]]]". sYields.
    mStoreT "hb1". sYields. mStoreT "hb2". sYields. mStoreT "hb3". sYields.
    cInlineT. rewrite /PQueueA.add. cStepsT.
    iMod (hinv_alloc (syn_data_inv hb cb cofs num reqid) _ _ (N.@"proxy".@"data")
      with "[hb1 hb2 hb3]") as "[%γh #data]".
    { solve_ndisj. }
    { rewrite sl_red; iFrame. }
    aForceT (N.@"queue") with "". iExists (_, _, _); iSplitR; first eauto with iFrame.
    iExists 1. iAuIntro. iInv "proxy" as "[%bins [%HQ [Q conts]]]". iAaccIntro with "Q". iSplit.
    { eauto with iFrame. }
    iIntros (ret_t) "/= Q !>"; iExists (tt↑); iSplit; [done|]. iSplitL.
    { iModIntro. iFrame "Q". rewrite length_insert HQ; iSplitR; [auto|].
      destruct (lookup_lt_is_Some_2 bins prt) as [lprt Hprt]; first lia.
      rewrite list_lookup_total_alt Hprt /=.
      iPoseProof (big_sepL_insert_acc with "[$]") as "[cont conts]"; first eauto.
      iApply ("conts" with "[-]"); simpl; iSplitL "help"; iFrame; eauto.
    }
    iModIntro. 
    iIntros "IST ->". cStepsT. sYields.
    iApply wsim_reset. cCoind CIH g Hg with reqid.
    iIntros "[#[queue [proxy data]] IST]".

    aUnfoldT. sYields.
    iEval (unfold IstFull; rewrite IstHelp_nested_equiv) in "IST".
    iInv "data" with "[IST]" as "[IST [[st|[st #Done]] ?]]" "close"; first (iFrame; eauto).
    { (* pending help *)
      mLoadT "st". iMod ("close" with "[//] [$] IST") as ">>IST".
      iEval (rewrite -IstHelp_nested_equiv) in "IST".
      sYields. iApply wsim_mem_cmp_int; [prove_inline_cond|solve_msk|].
      cStepsT. sYields.
      cByCoind CIH; eauto with iFrame.
    }
    mLoadT "st". iMod ("close" with "[//] [-IST] IST") as ">>IST".
    { iFrame "∗#"; eauto. }
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    sYields. iApply wsim_mem_cmp_int; [prove_inline_cond|solve_msk|].
    cStepsT. sYields. sYieldS. iApply (wsim_HelpDone_try_run with "Done").
    cStepsS. cStepsT.
    iApply wsim_unfold. iIntros "WINV". iApply wsim_ret. iFrame. eauto.
  Qed.

  Lemma proxy_simF : ⊢ ISim.sim_fun open
    (IOHelpM ★ Ctx)
    (IOHelpI ★ Ctx)
    IstFull (fid IOHdr.proxy).
  Proof.
    cStartFunSim. rewrite /ProxyI.proxy /ProxyM.proxy. cStepsS.
    aStepS (N q) "[-> [%sz [%qb [%qo [-> [%γq [#queue #proxy]]]]]]]".
    cStepsT. rewrite /sfunU. cStepsT. cStepsS. aAddY. sYields.
    iApply wsim_reset. cCoind CIH g Hg with sz.
    iIntros "[#[queue proxy] IST]".
    aUnfoldT. sYields. cInlineT. rewrite /PQueueA.remove_min. cStepsT.
    aForceT (N.@"queue") with ""; [instantiate (1:=(_, _)); s; iFrame "#"; done|s].
    replace 0 with (sz - sz) at 4 by lia.
    iAssert (⌜sz ≤ sz⌝)%I as "#Hsz"; first by subst.
    generalize sz at 3 10. iIntros (i). iInduction i as [|i].
    { aUnfoldT. sYields. rewrite decide_True //; last lia.
      cStepsT. sYields. cByCoind CIH; iFrame "IST"; eauto with iFrame.
    }
    iPoseProof "Hsz" as "%Hsz".
    aUnfoldT. sYields. rewrite decide_False //; last lia.
    cStepsT.
    iApply atomic_N_sem; [by simpl_sp|by simpl_sp|solve_msk|solve_msk|solve_ndisj|].
    iFrame "IST". iExists 1.
    iAuIntro. iInv "proxy" as "[%bins [%HQ [Q bins]]]". iAaccIntro with "Q".
    iSplit; first eauto with iFrame.
    iIntros (?) "[Q ->] !>"; iExists (tt↑); iSplitR; first done.
    destruct (lookup_lt_is_Some_2 bins (sz - S i)) as [lprt Hprt]; first lia.
    rewrite list_lookup_total_alt Hprt /=. destruct lprt as [|v lprt].
    { iSplitL.
      { iModIntro; iFrame. rewrite length_insert; iSplitR; first auto.
        rewrite list_insert_id //.
      }
      iIntros "!> IST".
      cStepsT. replace (S (sz - S i)) with (sz - i) by lia.
      iApply ("IHi" with "[] [$]").
      iPureIntro; lia.
    }
    iClear "IHi Hsz".
    simpl. iPoseProof (big_sepL_insert_acc with "bins") as "[bin bins]"; first eauto.
    iDestruct "bin" as "[[%reqid [%cb [%cfos [%num [Pend [%b [%γh [-> #data]]]]]]]] bin]".
    iPoseProof ("bins" with "bin") as "bins".
    iSplitL "Q bins"; first iFrame.
    { iPureIntro; rewrite length_insert //. }
    iModIntro; iIntros "IST".
    cStepsT. sYields. rewrite !left_id_L.
    iEval (unfold IstFull; rewrite IstHelp_nested_equiv) in "IST".
    iInv "data" with "[IST]" as "[IST [st [st2 stnum]]]" "close"; first (iFrame; eauto).
    mLoadT "st2".
    iMod ("close" with "[//] [$] IST") as ">>IST".
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    sYields.
    iEval (unfold IstFull; rewrite IstHelp_nested_equiv) in "IST".
    iInv "data" with "[IST]" as "[IST [? [? stnum]]]" "close"; first (iFrame; eauto).
    mLoadT "stnum".
    iMod ("close" with "[//] [$] IST") as ">>IST".
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    sYields. sYieldS. aUnfoldS. sYieldS. cStepsS. cInlineS. cStepsS.
    iApply (wsim_helping_help with "Pend").
    iExists 1. iModIntro.
    iApply wsim_reset. cCoind CIH2 g2 Hg2 with reqid.
    iIntros "[#[queue2 [proxy2 data]] [_ IST]]".
    replace ((cb, cfos, 0, num, None : option val)↑↑)
        with ((cb, cfos, num - num, num, None : option val)↑↑)
          by (f_equal; f_equal; f_equal; f_equal; lia).
    match goal with
    | |- context[ITree.iter ?body 0] => replace (ITree.iter body 0) with (ITree.iter body (num - num))
      by (f_equal; lia)
    end.
    iAssert (⌜num - num ≤ num⌝)%I as "%Hk"; first (iPureIntro; lia).
    revert Hk.
    generalize (num - num) at 1 2 3. intros k Hk.
    remember (num - k) as r eqn:Hr.
    iRevert (k Hk Hr) "IST".
    iInduction r as [|r]; iIntros (k Hk Hr) "IST".
    { (* base: k = num *)
      assert (k = num) by lia. subst k.
      aUnfoldS. aUnfoldT. sYield.
      rewrite /jobCode. cStepsS.
      rewrite Nat2Z.id decide_True //. cStepsT.
      sYieldS. cStepsS. rewrite decide_True //. cStepsS.
      cStep. iFrame.
      iIntros "#Done".
      cStepsS.
      aAddY. sYield.
      iEval (unfold IstFull; rewrite IstHelp_nested_equiv) in "IST".
      iInv "data" with "[IST]" as "[IST [[st0|[st0 #Done2]] [st1 st2]]]" "close2"; first (iFrame; eauto).
      - cStepsT. mStoreT "st0".
        iMod ("close2" with "[//] [- IST] IST") as ">>IST".
        { iFrame "∗#"; iRight; iFrame "∗#". }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        cStepsT.
        cByCoind CIH; iFrame "∗#"; eauto.
      - cStepsT. mStoreT "st0".
        iMod ("close2" with "[//] [- IST] IST") as ">>IST".
        { iFrame "∗#"; iRight; iFrame "∗#". }
        iEval (rewrite -IstHelp_nested_equiv) in "IST".
        cStepsT.
        cByCoind CIH; iFrame "∗#"; eauto.
    }
    (* step: k < num. Walks through one logical iter step (k → S k),
        pairing tgt's 4 yields per step (𝒴_a wrapper, 𝒴_b before load,
        𝒴_c between load and IO, 𝒴_d between IO and Ret) with src's two
        (one per jobCode call: None then Some v). The trailing 𝒴_d on
        tgt — after src.iter has recursed to (S k, None) — needs a 𝒴 on
        src.iter, supplied by helping_iter_prepend_yield_src above. *)
    aUnfoldS. aUnfoldT. sYield.
    rewrite /jobCode. cStepsS. rewrite Nat2Z.id.
    cStepsT. case_decide as Hcase2; first lia.
    sYield. sYieldS.
    cStepsS. case_decide as Hcase3; first lia. cStepsS.
    cStepsT. mLoadT "ASM".
    cForcesS; iFrame "ASM". cStepsS.
    aUnfoldS. sYield. sYieldS. cStepsS.
    cStep. cStepsS.
    appendRetS. iApply (helping_iter_prepend_yield_src (Some N)).
    rewrite bind_ret_r.
    sYield. sYieldS. cStepsT.
    iApply wsim_reset.
    iApply ("IHr" $! (S k) with "[] [] IST"); first iPureIntro; first lia.
    iPureIntro; lia.
  Qed.

  Lemma run_simF : ⊢ ISim.sim_fun open
    (IOHelpM ★ Ctx) (IOHelpI ★ Ctx)
    IstFull (funid (Helping.run mn)).
  Proof. cStartFunSim; cStepsT; ss. Qed.

  Lemma help_simF : ⊢ ISim.sim_fun open
    (IOHelpM ★ Ctx) (IOHelpI ★ Ctx)
    IstFull (funid (Helping.help mn)).
  Proof. cStartFunSim; cStepsT; ss. Qed.

  End SIM_FUNS.

  (* Combine the function-level simulations into a module-level ISim.t. *)
  Lemma sim : hinv_ownE ⊤ ⊢ ISim.t open
    (IOHelpM ★ Ctx)
    (IOHelpI ★ Ctx).
  Proof.
    iIntros "HE".
    iApply (ISim_reflR open IOHelpM IOHelpI Ctx
      (λ STATE, IstHelp (@IstEq Σ STATE IOHelpM) ⊤) with "[HE] []").
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT".
      rewrite /IstHelp. iFrame "HE".
      iApply (state_eq_init_same with "SRC TGT").
    - iIntros (STATE). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - mod_tac.
      }
      iIntros (fn) "%Hfn".
      repeat rewrite Mod.dom_fnsems_add in Hfn.
      unfold IOM.t, ProxyM.t, HelpingOn.t in Hfn.
      cbn in Hfn. set_unfold in Hfn; des; subst.
      + iApply init_simF.
      + iApply request_simF.
      + iApply proxy_simF.
      + iApply run_simF.
      + iApply help_simF.
  Qed.
End IOIM. End IOIM.

Module IOIA. Section IOIA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.
  Context (mn : string).
  Context (sp_user : specmap).

  Local Notation Mem := (CFilter.filter (Helping.exports mn) (MemA.t ∅)).
  Local Notation PQ := (CFilter.filter (Helping.exports mn) (PQueueA.t)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation IOACore := (IOA.t ★ ProxyA.t (SchA.sp sp_user ⊤)).
  Local Notation IOMCore :=
    ((IOM.t mn ★ ProxyM.t mn) ★ HelpingOff.t mn jobCode).
  Local Notation Ctx := ((PQ ★ Mem) ★ SchI).
  Local Notation IOA_mod := (IOACore ★ Ctx).
  Local Notation IOM_mod := (IOMCore ★ Ctx).
  Section SIM_FUNS.
  Context `{STATE : !stateGS Σ}.

  Local Definition IstMA : iProp Σ :=
    (state_init_tgt ({[mn]} : gset string) ∅ STATE ∗
     IstEq Ctx)%I.

  Lemma init_simFA : ⊢ ISim.sim_fun open
    IOA_mod IOM_mod
    IstMA (fid IOHdr.init).
  Proof.
    cStartFunSim. rewrite /IOA.init. cStepsS; cStepsT.
    aStepS (N sz) "[-> %Hsz]".
    aForceT N with ""; eauto.
    sYields. sYieldS.
    cStepsT. cForceS _q. cStepsS.
    rewrite /spawn_f.
    cStepsT. cForceS _q0. cStepsS.
    cStepsT. cStepsS.
    cForcesS. iFrame "GRT".
    cStepsS. cStepsT.
    cCall "IST" as (ret) "IST".
    destruct (Any.downcast ret); [cStepsT; cStepsS | cStepsT; cStepsS; destruct _q1].
    cForcesT; iFrame "ASM".
    cStepsT; iFrame; auto.
    cStepsS. cStepsT.
    iApply wsim_unfold. iIntros "WINV". iApply wsim_ret.
    iFrame "GRT"; iFrame; auto.
  Qed.

  Lemma request_simFA : ⊢ ISim.sim_fun open
    IOA_mod IOM_mod
    IstMA (fid IOHdr.request).
  Proof.
    cStartFunSim. rewrite /IOA.request /IOM.request. cStepsS; cStepsT.
    aStepS (N [[[q bofs] num] prt]) "[-> [%sz [#Hproxy %Hsz]]]".
    aForceT N with ""; first instantiate (1:=(q, bofs, num, prt)); s; eauto with iFrame.
    cStepsS. cStepsT. cInlineT. rewrite /HelpingOff.run.
    cStepsT.
    iApply wsim_reset. cCoind CIH g Hg with num.
    iIntros "[#Hproxy IST]".
    set (b1 := bofs.1). set (b2 := bofs.2).
    replace 0 with (num - num) at 1 by lia.
    replace ((b1, b2, 0, num, None : option val)↑↑)
       with ((b1, b2, num - num, num, None : option val)↑↑)
         by (f_equal; f_equal; f_equal; f_equal; lia).
    iAssert (⌜num - num ≤ num⌝)%I as "%Hk"; first (iPureIntro; lia).
    revert Hk.
    generalize (num - num) at 1 2 3. intros k Hk.
    remember (num - k) as r eqn:Hr.
    iRevert (k Hk Hr) "IST".
    iInduction r as [|r]; iIntros (k Hk Hr) "IST".
    { (* base: k = num *)
      assert (k = num) by lia. subst k.
      aUnfoldS. aUnfoldT. sYields.
      case_decide as Hcase; last lia.
      rewrite /jobCode. cStepsT.
      cStepsT. sYields. sYieldS. cStepsS. sYieldS. cStepsS. cStepsT.
      iApply wsim_unfold. iIntros "WINV". iApply wsim_ret. iFrame; auto.
    }
    (* step: k < num *)
    aUnfoldS; aUnfoldT. sYields.
    case_decide as Hcase; first lia.
    rewrite /jobCode. cStepsT.
    sYieldS.
    cStepsS. cForceT _q. cForcesT; iFrame "ASM". cStepsT.
    cForcesS; iFrame "GRT". aUnfoldT. sYields. sYieldS.
    cStep. cStepsS. cStepsT.
    iApply wsim_reset.
    iApply ("IHr" $! (S k) with "[] [] IST"); iPureIntro; lia.
  Qed.

  Lemma proxy_simFA : ⊢ ISim.sim_fun open
    IOA_mod IOM_mod
    IstMA (fid IOHdr.proxy).
  Proof.
    cStartFunSim. rewrite /ProxyA.proxy /ProxyM.proxy. s. cStepsS.
    destruct _q as [[mtid stid] []].
    iDestruct "ASM" as "[TID [%qptr [[-> ->] [%N [%sz Hproxy]]]]]".
    cStepsS. rewrite /sfunN. cStepsS. cStepsT.
    rewrite /atomic_fun.
    cForceT (N, qptr). cStepsT.
    cForcesT; iFrame "Hproxy"; eauto.
    iSplitR; first done.
    iApply wsim_reset. cNormS; cNormT. cCoind CIH g Hg with qptr.
    iIntros "[IST TID]".
    aUnfoldT. sYields. cInlineT. rewrite /HelpingOff.help; cStepsT.
    sYields. specialize (CIH qptr). cByCoind CIH. iFrame.
  Qed.

  End SIM_FUNS.

  (* Combine the IOA → IOM (helping-off) function-level simulations into
     a module-level ISim.t. *)
  Lemma sim : ⊢ ISim.t open
    IOA_mod IOM_mod.
  Proof.
    iApply (ISim_reflR open IOACore IOMCore Ctx
      (λ STATE, state_init_tgt ({[mn]} : gset string) ∅ STATE)).
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro.
        unfold Mod.add, IOA.t, ProxyA.t, IOM.t, ProxyM.t, HelpingOff.t;
          cbn.
        apply submseteq_nil_l.
      }
      iIntros "SRC TGT".
      assert (Hscopes :
        list_to_set (Mod.scopes IOMCore) = ({[mn]} : gset string)).
      { apply set_eq. intros scope.
        unfold Mod.add, IOM.t, ProxyM.t, HelpingOff.t; cbn. set_solver. }
      assert (Hinit : Mod.initial_st IOMCore = ∅).
      { unfold Mod.add, IOM.t, ProxyM.t, HelpingOff.t; cbn.
        apply map_eq. intros key. rewrite !lookup_union_with. simpl_map.
        reflexivity. }
      iEval (rewrite Hscopes Hinit) in "TGT".
      iExact "TGT".
    - iIntros (STATE). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - mod_tac.
      }
      iIntros (fn) "%Hfn".
      rewrite Mod.dom_fnsems_add in Hfn.
      unfold IOA.t, ProxyA.t in Hfn.
      cbn in Hfn. set_unfold in Hfn; des; subst.
      + iApply init_simFA.
      + iApply request_simFA.
      + iApply proxy_simFA.
  Qed.
End IOIA. End IOIA.

(* Contextual refinement: IOI ★ ProxyI refines IOA ★ ProxyA. *)
Module IOIA_ctxr. Section IOIA_ctxr.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.

  Lemma ctxr (sp : specmap) :
    help_init_cond ⊢
      ctx_refines
        ((IOI.t ★ ProxyI.t) ★ (PQueueA.t ★ MemA.t ∅) ★ SchI.t)
        ((IOA.t ★ ProxyA.t (SchA.sp sp ⊤)) ★ (PQueueA.t ★ MemA.t ∅) ★ SchI.t).
  Proof.
    iIntros "H".
    iApply (helping_main
      (λ mn, IOM.t mn ★ ProxyM.t mn)
      (IOA.t ★ ProxyA.t (SchA.sp sp ⊤))
      (IOI.t ★ ProxyI.t)
      (PQueueA.t ★ MemA.t ∅)
      jobCode with "H").
    iIntros (mn) "HE".
    { (* IOIM.sim — helping-on intermediate refinement *)
      rewrite !CFilter.filter_app.
      rewrite comm assoc (comm _ (HelpingDummy.t mn)).
      jIntros (ctx_refines_BiProset) "SRC".
      jPoseProof main_adequacy with "[HE]" "SRC" as "DST".
      { iApply (IOIM.sim mn). iFrame. }
      jDestruct "DST"
        as "(((IO & PROXY) & HELP) & ((PQ & MEM) & SCH))".
      jFrame.
    }
    iIntros (mn).
    { do 2 rewrite CFilter.filter_app.
      rewrite <-(mod_add_assoc
        (CFilter.filter (Helping.exports mn) PQueueA.t)
        (CFilter.filter (Helping.exports mn) (MemA.t ∅))
        (CFilter.filter (Helping.exports mn) SchI.t)).
      rewrite (Mod.add_comm
        (CFilter.filter (Helping.exports mn) PQueueA.t ★
         (CFilter.filter (Helping.exports mn) (MemA.t ∅) ★
          CFilter.filter (Helping.exports mn) SchI.t))
        (HelpingOff.t mn jobCode)).
      rewrite (mod_add_assoc
        (IOM.t mn ★ ProxyM.t mn)
        (HelpingOff.t mn jobCode)
        (CFilter.filter (Helping.exports mn) PQueueA.t ★
         (CFilter.filter (Helping.exports mn) (MemA.t ∅) ★
          CFilter.filter (Helping.exports mn) SchI.t))).
      rewrite !(mod_add_assoc
        (CFilter.filter (Helping.exports mn) PQueueA.t)
        (CFilter.filter (Helping.exports mn) (MemA.t ∅))
        (CFilter.filter (Helping.exports mn) SchI.t)).
      iApply main_adequacy.
      iApply (IOIA.sim mn sp).
    }
  Qed.
End IOIA_ctxr. End IOIA_ctxr.
