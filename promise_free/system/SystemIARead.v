Require Import CRIS.
Require Import SystemHeader SystemI SystemA.
Require Import PFMemHeader PFMemA HistoryRA AtomicRA.

Section SystemIA.
  Import SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.
  Context (sp_user sp : specmap).
  Context (size : list Z).
  Context (Hincl : sp_user ⊆ sp).
  Context (Hsysincl : (SystemA.sp sp_user ⊤) ⊆ sp).

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

  Lemma simF_read : ISim.sim_fun open SystemA_s SystemI_s IstFull (Some SystemHdr.read).
  Proof using.
    iStartSim.
    steps_l. destruct _q as [? ? [[X [-> ->]]|[X [-> ->]]]]; steps_l; unfold_pre_post.
    { ss; destruct X as [[[[[[tid stid] loc] ord] val] q] V]; ss.
      iDestruct "ASM" as "[-> [-> [PT TV]]]".
      iDestruct "TV" as "[TV STV]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".
      iPoseProof (tview_sys_lookup with "TA TV") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
        { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
        iDestruct "STV" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
      }
      subst.

      steps_r. rewrite /SystemI.get_tid. steps_r.
      inline_r. 
      unshelve force_r (FSpec_mk _ _ (or_introl _)).
      3:{ eexists (tid_cur, loc, ord, val, q, V); split; ss. }
      forces_r. iFrame. iDestruct "TA" as "[TA TVS]".
      rewrite big_sepM_delete //=. iDestruct "TVS" as "[$ TVS]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[-> [%v [%V' [[-> %] [↦ tv]]]]]".
      iCombine "TA" "TV" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA TidS]". 
      steps_r.
      forces_l. iFrame. iSplit; eauto.
      step.
      iSplit; eauto.
      iExists _, _, _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      iExists tid_cur, (<[tid_cur := (V', stid)]> tids); iSplit.
      { iPureIntro; split; rewrite ?fmap_insert /=; f_equal;
          rewrite ?insert_id // lookup_fmap Hlookup //. }
      rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
      iSplitL "TVS tv"; eauto.
      rewrite big_sepM_insert_delete; iFrame.
    }
    { ss.
      destruct X as [[[[[[[[[[[tid stid] loc] ord] ζ] ζ'] t0] γ] tx] mode] V] Vb].
      ss; unfold_pre_post.
      iDestruct "ASM" as "[-> [[-> %] [SN [PTS [Tid STid]]]]]".
      iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
      iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]". steps_r.
      iPoseProof (tview_sys_lookup with "TA Tid") as "%Hlookup"; first iFrame.
      destruct (decide (tid = tid_cur)); cycle 1.
      { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
        { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
        iDestruct "STid" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
      }
      subst.
      rewrite /SystemI.get_tid. steps_r. steps_r.
      inline_r.
      unshelve force_r (FSpec_mk _ _ (or_intror _)).
      3:{ eexists (tid_cur, loc, ord, _, _, _, _, _, _, _, _); split; ss. }
      forces_r. iFrame.
      iDestruct "TA" as "[TA TVS]".
      rewrite big_sepM_delete //. iDestruct "TVS" as "[$ TVS]"; eauto.
      iSplit; eauto.
      steps_r. iDestruct "GRT" as "[-> [% [% [% [% [% [% [% [[-> %] [SN [PTS TV]]]]]]]]]]]".
      iCombine "TA" "Tid" as "TA".
      iMod (own_update with "TA") as "TA".
      { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
      iDestruct "TA" as "[TA Tid]". 
      steps_r.
      forces_l. iFrame. iSplit; eauto. iSplit; eauto.
      iPureIntro; des; esplits; eauto.
      step.
      iSplit; eauto.
      iExists _, _, _, _; iSplit; eauto.
      iSplit; eauto.
      iSplit; eauto.
      iExists tid_cur, (<[tid_cur := (_, stid)]> tids); iSplit.
      { iPureIntro; split; rewrite ?fmap_insert /=; f_equal;
          rewrite ?insert_id // lookup_fmap Hlookup //. }
      rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
      iSplitL "TVS TV"; eauto.
      rewrite big_sepM_insert_delete; iFrame.
    }
  Unshelve. exact 1%Qp.
  (*SLOW*)Qed.
End SystemIA.