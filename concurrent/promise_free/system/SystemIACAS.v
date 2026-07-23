Require Import CRIS.common.CRIS.
From CRIS.promise_free.system Require Import SystemHeader SystemI SystemA.
From CRIS.promise_free.pfmem Require Import PFMemHeader PFMemA.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.

Section SystemIA.
  Import SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.
  Context (sp_user sp : specmap).
  Context (size : list Z).
  Context (Hincl : sp_user ⊆ sp).
  Context (Hsysincl : (SystemA.sp sp_user ⊤) ⊆ sp).

  Local Definition SystemA_s := SystemA.t sp_user ⊤ sp ★ PFMemA.t sp.
  Local Definition SystemI_s := SystemI.t ★ PFMemA.t sp.

  Definition Ist : ist_type Σ :=
    λ st_src st_tgt,
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)),
        let tids' : gmap Ident.t nat := snd <$> tids in
        ⌜st_tgt = {[SystemI.v_tid # tid↑; SystemI.v_tids # tids'↑]} ∧
         st_src = {[SystemI.v_tid # tid↑; SystemI.v_tids # tids'↑]}⌝ ∗
        tview_sys_auth tids ∗
        ([∗ map] i ↦ stid ∈ (snd <$> delete tid tids), YIELD stid))%I.

  Local Definition IstFull :=
    (IstProd (IstSB (Mod.scopes (SystemA.t sp_user ⊤ sp)) Ist) IstEq).

  Lemma simF_cas : ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.cas).
  Proof using.
    cStartFunSim. rewrite /SystemI.cas. cStepsS.
    destruct _q as [[[[[[[[[[[[[[tid stid] loc] old] new] ordr] ordw] V]
      γ] ζ'] Vb] tx] ζ] mode] Pr].
    iDestruct "ASM" as "[-> [PURE [TV [SN [PT [AW [PR CMP]]]]]]]".
    iDestruct "PURE" as "[-> %PRE]".
    iDestruct "TV" as "[Tid STV]".
    iDestruct "IST" as (????) "[[-> ->] [[% IST] ->]]".
    iDestruct "IST" as "[%tid_cur [%tids [[-> ->] [TA YS]]]]".

    iPoseProof (tview_sys_lookup with "TA Tid") as "%Hlookup"; first iFrame.
    destruct (decide (tid = tid_cur)); cycle 1.
    { iPoseProof (big_sepM_lookup_acc with "YS") as "[TV2 YS]".
      { instantiate (2:=tid). rewrite lookup_fmap lookup_delete_ne // Hlookup; ss. }
      iDestruct "STV" as "[_ Y2]".
      iPoseProof (YieldToken_both with "Y2 TV2") as "%"; done.
    }
    subst.

    cStepsT. rewrite /SystemI.get_tid. cStepsT. cInlineT.
    cForceT (tid_cur, loc, old, new, ordr, ordw, V, γ, ζ', Vb, tx, ζ, mode, Pr)%cris.
    iDestruct "TA" as "[TA TVS]".
    cForcesT. iFrame.
    rewrite big_sepM_delete //=. iDestruct "TVS" as "[$ TVS]"; eauto.
    iSplit; eauto.
    cStepsT.
    iDestruct "GRT" as
      "[-> [%ret [%ζ'' [%ζn [%t' [%f' [%LT [%v' [%Vr [%b [%V' [PURE [TV [SN [PR RESULT]]]]]]]]]]]]]]]".
    iDestruct "PURE" as "[-> %POST]".

    iCombine "TA" "Tid" as "TA".
    iMod (own_update with "TA") as "TA".
    { rewrite (gmap_view_replace _ tid_cur _ (to_agree _)) //. }
    iDestruct "TA" as "[TA Tid]".

    cForcesS.
    iSplitL "Tid STV SN PR RESULT".
    { iSplitR; first eauto.
      iExists ret, ζ'', ζn, t', f', LT, v', Vr, b, V'.
      iSplitR; first (iPureIntro; eauto).
      iFrame.
    }
    cStepsT.
    cStep.

    iSplit; eauto.
    iExists _, _, _, _; iSplit; eauto.
    iSplit; eauto.
    iSplit; eauto.
    iExists tid_cur, (<[tid_cur := (V', stid)]> tids); iSplit.
    { iPureIntro; split; rewrite fmap_insert /=; f_equal;
        rewrite insert_id // lookup_fmap Hlookup //.
    }
    rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
    iSplitL "TVS TV"; eauto.
    rewrite big_sepM_insert_delete; iFrame.
  Qed.
End SystemIA.
