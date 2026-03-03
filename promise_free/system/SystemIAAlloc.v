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
        ⌜st_tgt = {[SystemI.v_tid # tid↑; SystemI.v_tids # tids'↑]} ∧
         st_src = {[SystemI.v_tid # tid↑; SystemI.v_tids # tids'↑]}⌝ ∗
        tview_sys_auth tids ∗
        ([∗ map] i ↦ stid ∈ (snd <$> delete tid tids),
          (YIELD stid)))%I.

  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (SystemA.t sp_user ⊤ sp)) Ist) IstEq).

  Lemma simF_alloc : ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.alloc).
  Proof using.
    cStartFunSim. rewrite /SystemI.alloc.
    cStepsS. destruct _q as [[[tid ?] ?] ?]; iDestruct "ASM" as "[-> [-> TVS]]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".
    iDestruct "TVS" as "[Tid STV]".

    (* Current tid is my tid *)
    iPoseProof (tview_sys_lookup with "TA Tid") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
      { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
      iDestruct "STV" as "[_ Y2]"; iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
    }
    subst.

    cStepsT. rewrite /SystemI.get_tid. cStepsT.
    cInlineT. cForceT (_, _, _). cForcesT.
    iDestruct "TA" as "[TA TVS]".
    rewrite big_sepM_delete //. iDestruct "TVS" as "[$ TVS]"; eauto.
    iSplit; eauto.
    cStepsT. iDestruct "GRT" as "[-> [%loc [%V' [[-> %] [TV [FA MT]]]]]]".
    iCombine "TA" "Tid" as "TA".
    iMod (own_update with "TA") as "TA".
    { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
    iDestruct "TA" as "[TA Tid]". 
    cStepsT.
    cForcesS. iFrame. iSplit; eauto.
    cStep.

    (* IST *)
    iSplit; eauto.
    iExists _, _, _, _; iSplit; eauto.
    iSplit; eauto.
    iSplit; eauto.
    iExists tid_cur, (<[tid_cur := (V', n)]> tids); iSplit.
    { iPureIntro; split; f_equal; rewrite ?fmap_insert /= ?insert_id // lookup_fmap Hlookup //. }
    rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
    iSplitL "TVS TV"; eauto.
    rewrite big_sepM_insert_delete; iFrame.
  (*SLOW*)Qed.
End SystemIA.
