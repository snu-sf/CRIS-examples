Require Import CRIS.
Require Import SystemHeader SystemI SystemA.
Require Import SystemIAAlloc SystemIAWrite SystemIARead.
Require Import PFMemHeader PFMemA HistoryRA AtomicRA.

Module SystemIA. Section SystemIA.
  Import SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.
  Context (sp_user sp : specmap).
  Context (size : list Z).
  Context (Hincl : sp_user ⊆ sp).
  Context (Hsysincl : (SystemA.sp sp_user ⊤) ⊆ sp).
  Context (ConcInGlobal : speckey_concE ∈ dom sp).

  Local Definition SystemA_s := SystemA.t sp_user ⊤ sp ★ PFMemA.t sp.
  Local Definition SystemI_s := SystemI.t ★ PFMemA.t sp.
  Local Definition init_cond := init_cond size.

  Definition Ist : ist_type Σ :=
    λ st_src st_tgt,
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)),
        let tids' : gmap Ident.t nat := snd <$> tids in
        ⌜st_tgt = {[SystemI.v_tid := Some tid↑; SystemI.v_tids := Some tids'↑]} ∧
         st_src = {[SystemI.v_tid := Some tid↑; SystemI.v_tids := Some tids'↑]}⌝ ∗
        tview_sys_auth tids ∗
        ([∗ map] i ↦ stid ∈ (snd <$> delete tid tids),
          (YIELD stid)))%I.

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user ⊤ sp)) Ist) IstEq).

  Lemma simF__spawn : ISim.sim_fun open SystemA_s SystemI_s IstFull (Some SystemHdr._spawn).
  Proof using Hincl Hsysincl.
    iStartSim.
    steps_l. destruct _q as [].
    iDestruct "ASM" as
      "[%stid [%tid [%𝓥 [%pre [%fvarg [%farg [%fn [[-> ->] [W [[%fsp [% Spawn]] [TV PRE]]]]]]]]]]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA TVS]]]]".
    steps_l.
    unshelve erewrite (lookup_weaken _ _ _ _ _ Hincl); eauto.
    iDestruct ("Spawn" with "[]") as "[% [% [%Hfsp Hspawn]]]".
    { iPureIntro; exists (tid, stid); split; done. }
    iPoseProof ("Hspawn" with "[W PRE TV]") as "> [Pre Post]".
    { unfold_pre_post; iFrame; eauto. }
    force_l (FSpec_mk _ _ Hfsp); eauto. forces_l. iFrame.

    steps_l. steps_r. call "TA TVS".
    { iFrame. iExists _, _, _, _; repeat iSplit; eauto. }
    iIntros (ret st_src st_tgt) "IST".
    steps_l. steps_r.

    (* steps_l. steps_r. *)
    iMod ("Post" with "ASM") as "[W [% [_ TV]]] /=".

    rewrite /System.terminate; unseal "System".
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind; intros g' _ CIH [st_src st_tgt]; ss.
    destruct_quant CIH.

    iIntros "[IST [W TV]]".
    iPoseProof (winv_split_empty with "W") as "[W We]".

    unfold_iterC_l. steps_l. simpl_sp.
    iDestruct "TV" as "[%V TV]".
    force_l (tid, stid, V). steps_l. force_l (tt↑). steps_l.
    iApply wsim_fold; iFrame "W".
    force_l; iFrame "TV"; iSplit; eauto. steps_l.
    unfold_iterC_r. steps_r.
    call "IST". clear st_src st_tgt ret.
    iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[-> [-> TV]]". steps_l.
    steps_r.
    by_coind CIH; iFrame.
  (*SLOW*)Qed.

  Lemma simF_spawn : ISim.sim_fun open SystemA_s SystemI_s IstFull (Some SystemHdr.spawn).
  Proof using Hincl Hsysincl ConcInGlobal.
    iStartSim.

    steps_l. destruct _q as [[[tid stid] Post] V]. s.
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

    steps_r. steps_l.

    (* Calling PFMemHdr.spawn *)
    inline_r. steps_r.
    force_r (tid_cur, V). steps_r.
    force_r (tid_cur↑). steps_r.

    iDestruct "TA" as "[TA MTVS]".
    iPoseProof (big_sepM_lookup_acc with "MTVS") as "[MTV MTVS]"; eauto; ss.
    force_r; iFrame "MTV"; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[-> [%tid_new [-> [TV_cur TV_new]]]]".
    iPoseProof ("MTVS" with "TV_cur") as "MTVS".
    destruct (tids !! tid_new) as [[? ?]|] eqn : Hnew.
    { iPoseProof (big_sepM_lookup_acc _ _ tid_new with "MTVS") as "[TV_new2 MTVS]"; eauto.
      s; rewrite tview_eq /tview_def. iCombine "TV_new TV_new2" gives %WF%auth_frag_op_valid_1.
      rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF; done.
    }
    steps_r.

    unshelve (force_l (exist _ tid_new _)).
    { ss; rewrite lookup_fmap Hnew //. }
    steps_l. simpl_sp. case_decide; [|set_solver+ConcInGlobal]. forces_l. steps_l.
    iApply wsim_spawn. iIntros (nths). steps_l. steps_r.

    iMod (own_update with "TA") as "TA".
    { eapply (gmap_view_alloc _ tid_new (DfracOwn 1) (to_agree (V, nths))); ss.
      { rewrite ?lookup_fmap Hnew //. }
    }
    iDestruct "TA" as "[TA TVS_new]".

    force_l. iSplitL "TVS_new PRE Hspawn".
    { iIntros "? ? ?". iExists _, _, _, _, _, _, _. iFrame. iSplit; eauto. }
    steps_l.

    forces_l. iFrame "TV STV". iSplit; eauto. steps_l. step.
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

  Lemma simF_yield : ISim.sim_fun open SystemA_s SystemI_s IstFull (Some SystemHdr.yield).
  Proof using Hincl Hsysincl ConcInGlobal.
    iStartSim.

    steps_l. destruct _q as [[tid stid] V]. iDestruct "ASM" as "[-> [-> TV]]".
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
    subst. steps_l; steps_r.
    
    destruct _q as [[tid_next stid_next] Hin].
    force_l (exist _ (tid_next, stid_next) Hin). steps_l.

    case_decide; [|set_solver+ConcInGlobal]. s.
    force_l stid. steps_l.
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
    force_l; iFrame.

    steps_l; steps_r. case_decide; first set_solver. steps_r.
    iApply wsim_yield; iFrame. iSplit.
    { iExists _, _, st_tgtR, st_tgtR; iSplit; first ss. iSplit; eauto. }

    clear dependent tids.
    iIntros (st_src st_tgt) "IST".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur2 [%tids [[-> ->] [TA YS]]]]".
    steps_l. force_l (tt↑). step_l. iDestruct "ASM" as "[? [? ?]]".
    iApply wsim_fold; iFrame.
    force_l. iFrame. iSplit; eauto.

    steps_l; steps_r. step.
    iSplit; eauto.
    iExists _, _, _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iExists _, _; iSplit; first eauto.
    iFrame.
  (*SLOW*)Qed.

  Lemma simF_get_tid : ISim.sim_fun open SystemA_s SystemI_s IstFull (Some SystemHdr.get_tid).
  Proof using Hincl Hsysincl ConcInGlobal.
    iStartSim.

    steps_l. destruct _q as [[tid stid] V]. iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".
    steps_l; steps_r.

    (* v_tid is set to a correct one *)
    iDestruct "TV" as "[TV [TID Y]]".
    iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc _ _ tid with "YS") as "[Y2 YS]".
      { rewrite lookup_fmap lookup_delete_ne // Hlookup //. }
      iPoseProof (YieldToken_both with "Y2 Y") as "%"; done.
    }
    subst.
    force_l (tid_cur↑). steps_l. force_l. iFrame. iSplit; eauto. step. iSplit; eauto.

    iExists _, _, _, _; iSplit; first ss.
    iSplit; eauto.
    iSplit; eauto.
    iFrame. done.
  (*SLOW*)Qed.
End SystemIA.
Section ctx_refines.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.

  (* Scheduler for WM refines its specification when linked to WMM *)
  Lemma ctxr sp_user sp size :
    sp_user ⊆ sp →
    (SystemA.sp sp_user ⊤) ⊆ sp →
    speckey_concE ∈ dom sp →
    ctx_refines
      (SystemA.t sp_user ⊤ sp ★ PFMemA.t sp, init_cond size)
      (SystemI.t              ★ PFMemA.t sp, emp%I).
  Proof.
    intros ???.
    eapply main_adequacy with (Ist := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user ⊤ sp)) Ist) IstEq)).
    init_sim.
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