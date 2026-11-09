From CRIS.common Require Import CRIS.
From CRIS.promise_free.system Require Import
  SystemHeader SystemI SystemA SystemIAAlloc SystemIAWrite SystemIARead SystemIACAS.
From CRIS.promise_free.pfmem Require Import PFMemHeader PFMemA.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.

Module SystemIA. Section SystemIA.
  Import SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.
  Context (sp_user sp : specmap).
  Context (size : list Z).
  Context (Hincl : sp_user ⊆ sp).
  Context (Hsysincl : (SystemA.sp sp_user ⊤) ⊆ sp).
  Context (ConcInGlobal : sp.2).

  Local Definition SystemA_s := SystemA.t sp_user ⊤ sp ★ PFMemA.t sp.
  Local Definition SystemI_s := SystemI.t ★ PFMemA.t sp.
  Local Definition init_cond := init_cond size.

  Section SIM_FUNS.
    Context `{STGS : !stateGS Σ}.

  Definition Ist : iProp Σ :=
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)),
        let tids' : gmap Ident.t nat := snd <$> tids in
        SystemA.v_tid ↦src tid↑ ∗ SystemA.v_tids ↦src tids'↑ ∗
        SystemI.v_tid ↦tgt tid↑ ∗ SystemI.v_tids ↦tgt tids'↑ ∗
        tview_sys_auth tids ∗
        ([∗ map] i ↦ stid ∈ (snd <$> delete tid tids),
          (YIELD stid)))%I.

  Local Definition IstFull : iProp Σ :=
    (Ist ∗ IstEq (PFMemA.t sp))%I.

  Lemma simF__spawn :
    ⊢ ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr._spawn).
  Proof using Hincl Hsysincl.
    cStartFunSim. rewrite /SystemI._spawn.
    cStepsS. destruct _q as [].
    iDestruct "ASM" as
      "[%stid [%tid [%𝓥 [%pre [%fvarg [%farg [%fn [[-> ->] [W [[%fsp [% Spawn]] [TV PRE]]]]]]]]]]]".
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (tid_cur tids)
      "(TID_SRC & TIDS_SRC & TID_TGT & TIDS_TGT & TA & TVS)".
    cStepsS. simpl_sp.
    iDestruct ("Spawn" with "[] [W PRE TV]") as "> [% [% [%Hfsp [Pre Post]]]]".
    { iPureIntro; exists (tid, stid); split; done. } 
    { iFrame; iSplit; eauto. }
    cForceS (FSpec_mk _ _ Hfsp); eauto. cForcesS. iFrame.

    cStepsS. cStepsT.
    cCall "TID_SRC TIDS_SRC TID_TGT TIDS_TGT TA TVS EQ" as (ret) "IST".
    { iSplitR "EQ"; last iFrame. iExists _, _. iFrame. }
    cStepsS. cStepsT.

    (* cStepsS. cStepsT. *)
    iMod ("Post" with "ASM") as "[W [% [_ TV]]] /=".

    rewrite /System.terminate; unseal "System". iApply wsim_reset.
    cCoind CIH g' __ with tid_cur. iIntros "[IST [W TV]]".
    iPoseProof (winv_split_empty with "W") as "[W We]".

    rewrite {1 2}unfold_iterC. cStepsS. simpl_sp.
    iDestruct "TV" as "[%V TV]".
    cForceS (tid, stid, V). cStepsS. cForceS (tt↑). cStepsS.
    iApply wsim_fold; iFrame "W".
    cForceS; iFrame "TV"; iSplit; eauto. cStepsS.
    cStepsT.
    cCall "IST" as (ret) "IST".
    cStepsS. iDestruct "ASM" as "[-> [-> TV]]". cStepsS.
    cStepsT.
    specialize (CIH tid_cur).
    cByCoind CIH; iFrame.
  (*SLOW*)Qed.

  Lemma simF_spawn :
    ⊢ ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.spawn).
  Proof using Hincl Hsysincl ConcInGlobal.
    cStartFunSim. rewrite /SystemI.spawn.

    cStepsS. destruct _q as [[[tid stid] Post] V]. s.
    iDestruct "ASM" as "[%varg [-> [%fvarg [%farg [%fn [[-> ->] [Hspawn [TV PRE]]]]]]]]".
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (tid_cur tids)
      "(TID_SRC & TIDS_SRC & TID_TGT & TIDS_TGT & TA & TVS)".

    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV STV]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc with "TVS") as "[TV2 TVS]".
      { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
      iDestruct "STV" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
    }
    subst.

    cStepsT. cStepsS.
    cStepsS. cStepsT.
    set (tids_any := (((snd <$> tids : gmap Ident.t nat)↑) : Any.t)).
    subst tids_any.
    cStepsS. cStepsT.

    (* Calling PFMemHdr.spawn *)
    cInlineT. cStepsT.
    cForceT (tid_cur, V). cStepsT.
    cForceT (tid_cur↑). cStepsT.

    iDestruct "TA" as "[TA MTVS]".
    iPoseProof (big_sepM_lookup_acc with "MTVS") as "[MTV MTVS]"; eauto; ss.
    cForceT; iFrame "MTV"; iSplit; eauto.
    cStepsT. iDestruct "GRT" as "[-> [%tid_new [-> [TV_cur TV_new]]]]".
    iPoseProof ("MTVS" with "TV_cur") as "MTVS".
    destruct (tids !! tid_new) as [[? ?]|] eqn : Hnew.
    { iPoseProof (big_sepM_lookup_acc _ _ tid_new with "MTVS") as "[TV_new2 MTVS]"; eauto.
      s; rewrite tview_eq /tview_def. iCombine "TV_new TV_new2" gives %WF%auth_frag_op_valid_1.
      rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF; done.
    }
    cStepsT.
    cStepsS.

    unshelve (cForceS (exist _ tid_new _)).
    { ss; rewrite lookup_fmap Hnew //. }
    cStepsS. simpl_sp. rewrite ConcInGlobal. cForcesS. cStepsS.
    cSpawn as (nths). cStepsS. cForceS. cStepsS. cStepsT.

    iMod (own_update with "TA") as "TA".
    { eapply (gmap_view_alloc _ tid_new (DfracOwn 1) (to_agree (V, nths))); ss.
      { rewrite ?lookup_fmap Hnew //. }
    }
    iDestruct "TA" as "[TA TVS_new]".

    cForceS. iSplitL "TVS_new PRE Hspawn".
    { iIntros "? ? ?". iExists _, _, _, _, _, _, _. iFrame. iSplit; eauto. }
    cStepsS.
    cForcesS. iFrame "TV STV". iSplit; eauto. cStepsS. cStep.
    iSplit; eauto.
    iSplitR "EQ"; last iFrame.
    iExists tid_cur, (<[tid_new := (V, nths)]> tids).
    rewrite fmap_insert /=.
    iFrame "TID_SRC TIDS_SRC TID_TGT TIDS_TGT".
    rewrite -fmap_insert; iFrame "TA".
    iSplitL "TV_new MTVS".
    { iPoseProof (big_sepM_insert with "[TV_new MTVS]") as "$"; last iFrame; eauto. }
    { rewrite delete_insert_ne; cycle 1. { ii; clarify. }
      rewrite fmap_insert /= big_sepM_insert; first iFrame.
      rewrite lookup_fmap lookup_delete_ne; cycle 1. { ii; clarify. }
      rewrite Hnew //.
    }
  Unshelve. ss.
  (*SLOW*)Qed.

  Lemma simF_yield :
    ⊢ ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.yield).
  Proof using Hincl Hsysincl ConcInGlobal.
    cStartFunSim. rewrite /SystemI.yield /yield.

    cStepsS. destruct _q as [[tid stid] V]. iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (tid_cur tids)
      "(TID_SRC & TIDS_SRC & TID_TGT & TIDS_TGT & TA & YS)".
    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV [TID Y]]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc _ _ tid with "YS") as "[Y2 YS]".
      { rewrite lookup_fmap lookup_delete_ne // Hlookup //. }
      iPoseProof (YieldToken_both with "Y2 Y") as "%"; done.
    }
    subst. cStepsS; cStepsT.
    set (tids_any := (((snd <$> tids : gmap Ident.t nat)↑) : Any.t)).
    subst tids_any.
    cStepsS; cStepsT.
    
    destruct _q as [[tid_next stid_next] Hin].
    cForceS (exist _ (tid_next, stid_next) Hin). cStepsS.

    rewrite ConcInGlobal. s. cStepsS. cStepsT.
    cForceS stid. cStepsS.
    iAssert (YIELD stid_next ∗
        [∗ map] i ↦ e ∈ (snd <$> delete tid_next tids), YIELD e)%I
      with "[Y YS]" as "[Y YS]".
    { destruct (decide (tid_cur = tid_next)). 
      { subst. rewrite lookup_fmap Hlookup in Hin; ss; clarify.
        destruct (tids !! tid_next) as [[[? ?] ?]|]; ss. iFrame.
      }
      rewrite fmap_delete.
      iPoseProof (big_sepM_insert_delete with "[Y YS]") as "YS".
      { iSplitL "Y"; iFrame; ss. }
      iPoseProof (big_sepM_delete _ _ tid_next with "YS") as "[$ YS]".
      { rewrite lookup_insert_ne //. }
      rewrite (insert_id (snd <$> tids) tid_cur). 2:{ rewrite lookup_fmap Hlookup //. }
      rewrite fmap_delete //.
    }
    iApply wsim_unfold; iIntros "W".
    cForceS; iFrame.

    cStepsS; cStepsT. cStepsT.
    iApply wsim_yield; iFrame.

    clear dependent tids.
    iIntros "IST".
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (tid_cur2 tids)
      "(TID_SRC & TIDS_SRC & TID_TGT & TIDS_TGT & TA & YS)".
    cStepsS. cForceS (tt↑). iDestruct "ASM" as "[? [? ?]]".
    iApply wsim_fold; iFrame.
    cForceS. iFrame. iSplit; eauto.

    cStepsS; cStepsT. cStep.
    iSplit; eauto.
    iSplitR "EQ"; last iFrame.
    iExists tid_cur2, tids. iFrame.
  (*SLOW*)Qed.

  Lemma simF_get_tid :
    ⊢ ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.get_tid).
  Proof using Hincl Hsysincl ConcInGlobal.
    cStartFunSim. rewrite /SystemI.get_tid /get_tid.

    cStepsS. destruct _q as [[tid stid] V]. iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (tid_cur tids)
      "(TID_SRC & TIDS_SRC & TID_TGT & TIDS_TGT & TA & YS)".
    cStepsS; cStepsT.
    cStepsS; cStepsT.

    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV [TID Y]]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc _ _ tid with "YS") as "[Y2 YS]".
      { rewrite lookup_fmap lookup_delete_ne // Hlookup //. }
      iPoseProof (YieldToken_both with "Y2 Y") as "%"; done.
    }
    subst.
    cForceS (tid_cur↑). cStepsS. cForceS. iFrame. iSplit; eauto. cStep. iSplit; eauto.

    iSplitR "EQ"; last iFrame.
    iExists tid_cur, tids. iFrame.
  (*SLOW*)Qed.
  End SIM_FUNS.

End SystemIA.
Section ctx_refines.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.

  (* Scheduler for WM refines its specification when linked to WMM *)
  Lemma ctxr (sp_user sp: specmap) size :
    sp_user ⊆ sp →
    (SystemA.sp sp_user ⊤) ⊆ sp →
    sp.2 →
    init_cond size ⊢
      ctx_refines
        (SystemI.t ★ PFMemA.t sp)
        (SystemA.t sp_user ⊤ sp ★ PFMemA.t sp).
  Proof.
    intros ???.
    etrans; cycle 1.
    { eapply (main_adequacy
        (SystemI.t ★ PFMemA.t sp)
        (SystemA.t sp_user ⊤ sp ★ PFMemA.t sp)). }
    iIntros "TA".
    iApply (ISim_reflR open
      (SystemA.t sp_user ⊤ sp) SystemI.t (PFMemA.t sp)
      (fun STGS : stateGS Σ => Ist (STGS := STGS))
      with "[TA] []").
    - iIntros (STGS). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT".
      iEval (rewrite /state_init_src /=) in "SRC".
      iEval (rewrite /state_init_tgt /=) in "TGT".
      assert (SLS : state_slice ({["System"]} : gset string)
          {[SystemA.v_tid # 1%positive↑;
            SystemA.v_tids # ({[1%positive := 0]} : tidmap)↑]} =
          {[SystemA.v_tid := 1%positive↑;
            SystemA.v_tids := ({[1%positive := 0]} : tidmap)↑]}).
      { apply map_eq. intros k. rewrite state_slice_lookup.
        destruct (decide (k = SystemA.v_tid)); subst; simpl_map.
        - case_decide; done.
        - destruct (decide (k = SystemA.v_tids)); subst; simpl_map.
          + case_decide; done.
          + repeat case_decide; done.
      }
      assert (SLT : state_slice ({["System"]} : gset string)
          {[SystemI.v_tid # 1%positive↑;
            SystemI.v_tids # ({[1%positive := 0]} : tidmap)↑]} =
          {[SystemI.v_tid := 1%positive↑;
            SystemI.v_tids := ({[1%positive := 0]} : tidmap)↑]}).
      { exact SLS. }
      iEval (rewrite right_id_L SLS) in "SRC".
      iEval (rewrite right_id_L SLT) in "TGT".
      iDestruct "SRC" as "[SRC _]".
      iEval (rewrite big_sepM_insert) in "SRC"; last simpl_map.
      iDestruct "SRC" as "[TID_SRC TIDS_SRC]".
      iEval (rewrite big_sepM_singleton) in "TIDS_SRC".
      iDestruct "TGT" as "[TGT _]".
      iEval (rewrite big_sepM_insert) in "TGT"; last simpl_map.
      iDestruct "TGT" as "[TID_TGT TIDS_TGT]".
      iEval (rewrite big_sepM_singleton) in "TIDS_TGT".
      iExists 1%positive, {[1%positive := (TView.init size, 0)]}.
      iFrame "TID_SRC TIDS_SRC TID_TGT TIDS_TGT".
      rewrite delete_singleton fmap_empty big_sepM_empty. iFrame "TA".
    - iIntros (STGS). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split; mod_tac. }
      iIntros (fn) "%Hfn".
      set_unfold in Hfn; des; subst.
      + iApply simF__spawn; eauto.
      + iApply simF_spawn; eauto.
      + iApply simF_yield; eauto.
      + iApply simF_get_tid; eauto.
      + iApply simF_alloc; eauto.
      + iApply simF_write; eauto.
      + iApply simF_read; eauto.
      + iApply simF_cas; eauto.
  Qed.
End ctx_refines. End SystemIA.
