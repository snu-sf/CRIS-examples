Require Import CRIS.
Require Import SystemHeader SystemI SystemA.
Require Import SystemIAAlloc SystemIAWrite SystemIARead.
Require Import PFMemHeader PFMemA HistoryRA AtomicRA.

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

  Definition Ist : ist_type Σ :=
    λ st_src st_tgt,
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)),
        let tids' : gmap Ident.t nat := snd <$> tids in
        ⌜st_tgt = {[SystemI.v_tid # tid↑; SystemI.v_tids # tids'↑]} ∧
         st_src = {[SystemI.v_tid # tid↑; SystemI.v_tids # tids'↑]}⌝ ∗
        tview_sys_auth tids ∗
        ([∗ map] i ↦ stid ∈ (snd <$> delete tid tids),
          (YIELD stid)))%I.

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user ⊤ sp)) Ist) IstEq).

  Lemma simF__spawn : ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr._spawn).
  Proof using Hincl Hsysincl.
    cStartFunSim. rewrite /SystemI._spawn.
    cStepsS. destruct _q as [].
    iDestruct "ASM" as
      "[%stid [%tid [%𝓥 [%pre [%fvarg [%farg [%fn [[-> ->] [W [[%fsp [% Spawn]] [TV PRE]]]]]]]]]]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA TVS]]]]".
    cStepsS. simpl_sp.
    iDestruct ("Spawn" with "[] [W PRE TV]") as "> [% [% [%Hfsp [Pre Post]]]]".
    { iPureIntro; exists (tid, stid); split; done. } 
    { iFrame; iSplit; eauto. }
    cForceS (FSpec_mk _ _ Hfsp); eauto. cForcesS. iFrame.

    cStepsS. cStepsT. cCall "TA TVS" as (ret st_src st_tgt) "IST".
    { iFrame. iExists _, _, _, _; repeat iSplit; eauto. }
    cStepsS. cStepsT.

    (* cStepsS. cStepsT. *)
    iMod ("Post" with "ASM") as "[W [% [_ TV]]] /=".

    rewrite /System.terminate; unseal "System". iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt. iIntros "[IST [W TV]]".
    iPoseProof (winv_split_empty with "W") as "[W We]".

    unfoldIterCS. cStepsS. simpl_sp.
    iDestruct "TV" as "[%V TV]".
    cForceS (tid, stid, V). cStepsS. cForceS (tt↑). cStepsS.
    iApply wsim_fold; iFrame "W".
    cForceS; iFrame "TV"; iSplit; eauto. cStepsS.
    unfoldIterCT. cStepsT.
    cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsS. iDestruct "ASM" as "[-> [-> TV]]". cStepsS.
    cStepsT.
    cByCoind CIH; iFrame.
  (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.spawn).
  Proof using Hincl Hsysincl ConcInGlobal.
    cStartFunSim. rewrite /SystemI.spawn.

    cStepsS. destruct _q as [[[tid stid] Post] V]. s.
    iDestruct "ASM" as "[%varg [-> [%fvarg [%farg [%fn [[-> ->] [Hspawn [TV PRE]]]]]]]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA TVS]]]]".

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
    iExists _, _, st_tgtR, st_tgtR; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iExists tid_cur, (<[tid_new := (V, nths)]> tids).
    rewrite -?fmap_insert /=.
    (* iSplit; eauto. *)
    rewrite ?fmap_insert /=; iSplit; eauto; iFrame.
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

  Lemma simF_yield : ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.yield).
  Proof using Hincl Hsysincl ConcInGlobal.
    cStartFunSim. rewrite /SystemI.yield /yield.

    cStepsS. destruct _q as [[tid stid] V]. iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".

    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV [TID Y]]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc _ _ tid with "YS") as "[Y2 YS]".
      { rewrite lookup_fmap lookup_delete_ne // Hlookup //. }
      iPoseProof (YieldToken_both with "Y2 Y") as "%"; done.
    }
    subst. cStepsS; cStepsT.
    
    destruct _q as [[tid_next stid_next] Hin].
    cForceS (exist _ (tid_next, stid_next) Hin). cStepsS.

    rewrite ConcInGlobal. s.
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
    iApply wsim_yield; iFrame. iSplit.
    { iExists _, _, st_tgtR, st_tgtR; iSplit; first ss. iSplit; eauto. }

    clear dependent tids.
    iIntros (st_src st_tgt) "IST".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur2 [%tids [[-> ->] [TA YS]]]]".
    cStepsS. cForceS (tt↑). cStepS. iDestruct "ASM" as "[? [? ?]]".
    iApply wsim_fold; iFrame.
    cForceS. iFrame. iSplit; eauto.

    cStepsS; cStepsT. cStep.
    iSplit; eauto.
    iExists _, _, _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iExists _, _; iSplit; first eauto.
    iFrame.
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.get_tid).
  Proof using Hincl Hsysincl ConcInGlobal.
    cStartFunSim. rewrite /SystemI.get_tid /get_tid.

    cStepsS. destruct _q as [[tid stid] V]. iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".
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

    iExists _, _, _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iFrame. done.
  (*SLOW*)Qed.
End SystemIA.
Section ctx_refines.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.

  (* Scheduler for WM refines its specification when linked to WMM *)
  Lemma ctxr (sp_user sp: specmap) size :
    sp_user ⊆ sp →
    (SystemA.sp sp_user ⊤) ⊆ sp →
    sp.2 →
    ctx_refines
      (SystemI.t              ★ PFMemA.t sp, emp%I)
      (SystemA.t sp_user ⊤ sp ★ PFMemA.t sp, init_cond size).
  Proof.
    intros ???.
    eapply main_adequacy with (Ist := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user ⊤ sp)) Ist) IstEq)).
    cStartModSim.
    { apply simF__spawn; eauto. }
    { apply simF_spawn; eauto. }
    { apply simF_yield; eauto. }
    { apply simF_get_tid; eauto. }
    { apply simF_alloc; eauto. }
    { apply simF_write; eauto. }
    { apply simF_read; eauto. }
    { iIntros "TA"; repeat iExists _; repeat iSplit; ss.
      iExists 1%positive, {[1%positive := (TView.init size, 0)]}; iFrame.
      iSplit; first eauto.
      rewrite delete_singleton fmap_empty //.
    }
  Qed.
End ctx_refines. End SystemIA.
