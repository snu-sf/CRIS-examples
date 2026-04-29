Require Import CRIS ImpPrelude.
Require Import IOHeader IOI IOA.
Require Import MemHeader SchHeader PQueueHeader IOHeader.
Require Import Atomic SchA SchTactics.
Require Import PQueueA StackA MemA.
Require Import MemTactics.
Require Import HelpingTactics HelpingFacts.
Require Import SchI.

(* Helper lemma: prepend a 𝒴@{N} to ITree.iter whose body starts with 𝒴@{N}.
   Same idea as yield_iter_prepend_yield_src but for the form induced by
   wsim_helping_help (plain ITree.iter without the trailing 𝒴+Ret). *)
Lemma helping_iter_prepend_yield_src `{!crisG Γ Σ α β τ Hinv Hsub}
    (N : option namespace)
    {I R : Type} (body : I → itree crisE (I + R)) (arg : I)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (Es : coPset) r g
    {R_s R_t} (RR : WSim.post R_s R_t)
    (msk_s : emask)
    (sp_s : specmap)
    (ktr_s : R → itree crisE R_s)
    (itr_t : itree crisE R_t) :
  wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) 𝒴@{N});;;
      ⇓sbox(msk_s) (⇓smod(sp_s) (ITree.iter (λ a : I, 𝒴@{N};;; body a) arg)) >>= ktr_s)
    (st_tgt, itr_t) ⊢
  wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) (ITree.iter (λ a : I, 𝒴@{N};;; body a) arg)) >>= ktr_s)
    (st_tgt, itr_t).
Proof.
  iIntros "SIM". rewrite unfold_iter_eq. cNormS. iApply wsim_yy_y_namespace.
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
  Local Definition IstFull : ist_type Σ := IstHelp mn ⊤.

  Lemma init_simF : ISim.sim_fun open
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOn.t mn jobCode) ★ (PQ ★ Mem) ★ SchI)
    (((IOI ★ ProxyI) ★ HelpingDummy.t mn) ★ (PQ ★ Mem) ★ SchI)
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
    iIntros (tid ??) "IST J". cStep; iFrame "∗#"; eauto.
  Qed.

  Lemma request_simF : ISim.sim_fun open
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOn.t mn jobCode) ★ (PQ ★ Mem) ★ SchI)
    (((IOI ★ ProxyI) ★ HelpingDummy.t mn) ★ (PQ ★ Mem) ★ SchI)
    IstFull (fid IOHdr.request).
  Proof.
    cStartFunSim. rewrite /IOM.request /IOI.request. cStepsS.
    aStepS (N [[[q [cb cofs]] num] prt]) "[-> [%sz [[%qb [%qofs [-> [%γq [#queue #proxy]]]]] %Hsz]]]".
    cStepsS; cStepsT.
    iApply (wsim_helping_run with "IST"); [simpl_map; s; f_equal|].
    clear_st; iIntros (st_src reqid) "IST help". sYields.
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
    clear_st; iIntros (st_src st_tgt) "IST ->". cStepsT. sYields.
    iApply wsim_reset. cCoind CIH g Hg with st_src st_tgt.
    iIntros "[#[queue [proxy data]] IST]".

    aUnfoldT. sYields.
    iInv "data" with "[IST]" as "[IST [[st|[st #Done]] ?]]" "close"; first (iFrame; eauto).
    { (* pending help *)
      mLoadT "st". iMod ("close" with "[//] [$] IST") as ">>IST".
      sYields. iApply wsim_mem_cmp_int; [simpl_map; s; f_equal|solve_msk|].
      cStepsT. sYields.
      cByCoind CIH; eauto with iFrame.
    }
    mLoadT "st". iMod ("close" with "[//] [-IST] IST") as ">>IST".
    { iFrame "∗#"; eauto. }
    sYields. iApply wsim_mem_cmp_int; [simpl_map; s; f_equal|solve_msk|].
    cStepsT. sYields. sYieldS. iApply (wsim_HelpDone_try_run with "[$] [$]").
    iIntros "IST"; cStepsS. cStep; iFrame. eauto.
  Qed.

  Lemma proxy_simF : ISim.sim_fun open
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOn.t mn jobCode) ★ (PQ ★ Mem) ★ SchI)
    (((IOI ★ ProxyI) ★ HelpingDummy.t mn) ★ (PQ ★ Mem) ★ SchI)
    IstFull (fid IOHdr.proxy).
  Proof.
    cStartFunSim. rewrite /ProxyI.proxy /ProxyM.proxy. cStepsS.
    aStepS (N q) "[-> [%sz [%qb [%qo [-> [%γq [#queue #proxy]]]]]]]".
    cStepsT. rewrite /sfunU. cStepsT. cStepsS. aAddY. sYields.
    iApply wsim_reset. cCoind CIH g Hg with st_src st_tgt.
    iIntros "[#[queue proxy] IST]".
    aUnfoldT. sYields. cInlineT. rewrite /PQueueA.remove_min. cStepsT.
    aForceT (N.@"queue") with ""; [instantiate (1:=(_, _)); s; iFrame "#"; done|s].
    replace 0 with (sz - sz) at 4 by lia.
    iAssert (⌜sz ≤ sz⌝)%I as "#Hsz"; first by subst.
    generalize sz at 3 10. iIntros (i). iInduction i as [|i] forall (st_src st_tgt).
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
      clear_st; iIntros "!> %% IST".
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
    iModIntro; clear_st; iIntros (st_src0 st_tgt0) "IST".
    cStepsT. sYields. rewrite !left_id_L.
    iInv "data" with "[IST]" as "[IST [st [st2 stnum]]]" "close"; first (iFrame; eauto).
    mLoadT "st2".
    iMod ("close" with "[//] [$] IST") as ">>IST".
    sYields.
    iInv "data" with "[IST]" as "[IST [? [? stnum]]]" "close"; first (iFrame; eauto).
    mLoadT "stnum".
    iMod ("close" with "[//] [$] IST") as ">>IST".
    sYields. sYieldS. aUnfoldS. sYieldS. cStepsS. cInlineS. cStepsS.
    iApply (wsim_helping_help with "Pend IST").
    iExists 1. clear_st; iIntros (st_src) "IST !>".
    iApply wsim_reset. cCoind CIH2 g2 Hg2 with st_src st_tgt0.
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
    iInduction r as [|r] forall (st_src st_tgt0); iIntros (k Hk Hr) "IST".
    { (* base: k = num *)
      assert (k = num) by lia. subst k.
      aUnfoldS. aUnfoldT. sYield.
      rewrite /jobCode. cStepsS.
      rewrite Nat2Z.id decide_True //. cStepsT.
      sYieldS. cStepsS. rewrite decide_True //. cStepsS.
      cStep. iExists ⊤. iFrame.
      iIntros (st_src1 st_tgt) "#Done IST".
      cStepsS.
      aAddY. sYield.
      iInv "data" with "[IST]" as "[IST [[st0|[st0 #Done2]] [st1 st2]]]" "close2"; first (iFrame; eauto).
      - cStepsT. mStoreT "st0".
        iMod ("close2" with "[//] [- IST] IST") as ">>IST".
        { iFrame "∗#"; iRight; iFrame "∗#". }
        cStepsT.
        cByCoind CIH; iFrame "∗#"; eauto.
      - cStepsT. mStoreT "st0".
        iMod ("close2" with "[//] [- IST] IST") as ">>IST".
        { iFrame "∗#"; iRight; iFrame "∗#". }
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
    iApply ("IHr" $! _ _ (S k) with "[] [] IST"); first iPureIntro; first lia.
    iPureIntro; lia.
  Qed.

  (* Combine the function-level simulations into a module-level ISim.t. *)
  Lemma sim : ISim.t open
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOn.t mn jobCode) ★ (PQ ★ Mem) ★ SchI)
    (((IOI ★ ProxyI) ★ HelpingDummy.t mn) ★ (PQ ★ Mem) ★ SchI)
    help_init_cond IstFull.
  Proof.
    cStartModSim.
    { apply init_simF. }
    { apply request_simF. }
    { apply proxy_simF. }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    { cStartFunSim; cStepsT. cStepsT; ss. }
    { iIntros "[? ?]"; repeat iExists _; iFrame; iPureIntro; splits; eauto; ss.
      { rewrite !dom_union_with !dom_empty_L !dom_singleton_L. set_solver. }
      { exists ∅. rewrite !left_id_L !right_id_L //. }
    }
  Qed.
End IOIM. End IOIM.

Module IOIA. Section IOIA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.
  Context (mn : string).
  Context (sp_user : specmap).

  Local Notation Mem := (CFilter.filter (Helping.exports mn) (MemA.t ∅)).
  Local Notation PQ := (CFilter.filter (Helping.exports mn) (PQueueA.t)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Definition IstMA : ist_type Σ :=
    IstProd (IstSB (Mod.scopes (IOA.t) ++ [mn]) IstTrue) IstEq.

  Local Notation IOA_mod :=
    ((IOA.t ★ ProxyA.t (SchA.sp sp_user ⊤)) ★ PQ ★ Mem ★ SchI).
  Local Notation IOM_mod :=
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOff.t mn jobCode) ★ PQ ★ Mem ★ SchI).

  Lemma init_simFA : ISim.sim_fun open
    ((IOA.t ★ ProxyA.t (SchA.sp sp_user ⊤)) ★ PQ ★ Mem ★ SchI)
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOff.t mn jobCode) ★ PQ ★ Mem ★ SchI)
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
    cCall "IST" as (ret st_src1 st_tgt1) "IST".
    destruct (Any.downcast ret); [cStepsT; cStepsS | cStepsT; cStepsS; destruct _q1].
    cForcesT; iFrame "ASM".
    cStepsT; iFrame; auto.
    cStep; iFrame "GRT"; iFrame; auto.
  Qed.

  Lemma request_simFA : ISim.sim_fun open
    ((IOA.t ★ ProxyA.t (SchA.sp sp_user ⊤)) ★ PQ ★ Mem ★ SchI)
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOff.t mn jobCode) ★ PQ ★ Mem ★ SchI)
    IstMA (fid IOHdr.request).
  Proof.
    cStartFunSim. rewrite /IOA.request /IOM.request. cStepsS; cStepsT.
    aStepS (N [[[q bofs] num] prt]) "[-> [%sz [#Hproxy %Hsz]]]".
    aForceT N with ""; first instantiate (1:=(q, bofs, num, prt)); s; eauto with iFrame.
    cStepsS. cStepsT. cInlineT. rewrite /HelpingOff.run.
    cStepsT.
    iApply wsim_reset. cCoind CIH g Hg with st_src st_tgt.
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
    iInduction r as [|r] forall (st_src st_tgt); iIntros (k Hk Hr) "IST".
    { (* base: k = num *)
      assert (k = num) by lia. subst k.
      aUnfoldS. aUnfoldT. sYields.
      case_decide as Hcase; last lia.
      rewrite /jobCode. cStepsT.
      case_decide as Hcase2; last lia.
      cStepsT. sYields. sYieldS. cStepsS. sYieldS. cStep; iFrame; auto.
    }
    (* step: k < num *)
    aUnfoldS; aUnfoldT. sYields.
    case_decide as Hcase; first lia.
    rewrite /jobCode. cStepsT.
    case_decide as Hcase2; first lia.
    sYieldS.
    cStepsS. cForceT _q. cForcesT; iFrame "ASM". cStepsT.
    cForcesS; iFrame "GRT". aUnfoldT. sYields. sYieldS.
    cStep. cStepsS. cStepsT.
    iApply wsim_reset.
    iApply ("IHr" $! _ _ (S k) with "[] [] IST"); iPureIntro; lia.
  Qed.

  Lemma proxy_simFA : ISim.sim_fun open
    ((IOA.t ★ ProxyA.t (SchA.sp sp_user ⊤)) ★ PQ ★ Mem ★ SchI)
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOff.t mn jobCode) ★ PQ ★ Mem ★ SchI)
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
    iApply wsim_reset. cCoind CIH g Hg with st_src st_tgt.
    iIntros "[IST TID]".
    aUnfoldT. sYields. cInlineT. rewrite /HelpingOff.help; cStepsT.
    sYields. cByCoind CIH. iFrame.
  Qed.

  (* Combine the IOA → IOM (helping-off) function-level simulations into
     a module-level ISim.t. *)
  Lemma sim : ISim.t open
    ((IOA.t ★ ProxyA.t (SchA.sp sp_user ⊤)) ★ PQ ★ Mem ★ SchI)
    (((IOM.t mn ★ ProxyM.t mn) ★ HelpingOff.t mn jobCode) ★ PQ ★ Mem ★ SchI)
    emp%I IstMA.
  Proof.
    cStartModSim.
    { apply init_simFA. }
    { apply request_simFA. }
    { apply proxy_simFA. }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.
End IOIA. End IOIA.

(* Contextual refinement: IOI ★ ProxyI refines IOA ★ ProxyA. *)
Module IOIA_ctxr. Section IOIA_ctxr.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.

  Lemma ctxr (sp : specmap) :
    ctx_refines
      ((IOI.t ★ ProxyI.t) ★ (PQueueA.t ★ MemA.t ∅) ★ SchI.t, emp%I)
      ((IOA.t ★ ProxyA.t (SchA.sp sp ⊤)) ★ (PQueueA.t ★ MemA.t ∅) ★ SchI.t,
        help_init_cond).
  Proof.
    etrans; cycle 1; first eapply ctxr_consequence.
    { instantiate (1:=(_ ∗ emp)%I); iIntros "H"; iSplitL; last done; iExact "H". }
    etrans; first eapply (helping_main) with
      (mM := λ mn, IOM.t mn ★ ProxyM.t mn)
      (mE := PQueueA.t ★ MemA.t ∅)
      (jobs := jobCode); [intros mn|intros mn|..].
    { (* IOIM.sim — helping-on intermediate refinement *)
      rewrite !CFilter.filter_app.
      rewrite comm assoc (comm _ (HelpingDummy.t mn)).
      etrans; [eapply main_adequacy, IOIM.sim|].
      ctxr_norm. do 2 ctxr_drop. ctxr_rotate. refl.
    }
    { etrans.
      { do 3 ctxr_rotate. ctxr_swap. ctxr_rotate; ctxr_swap. do 3 ctxr_rotate. refl. }
      rewrite !CFilter.filter_app; do 2 rewrite assoc.
      etrans; [eapply main_adequacy, IOIA.sim|].
      rewrite -!assoc; eauto. rewrite assoc. refl.
    }
    eapply ctxr_consequence; iIntros "[$ _]".
  Qed.
End IOIA_ctxr. End IOIA_ctxr.