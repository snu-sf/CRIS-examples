From CRIS.common Require Import CRIS.
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
  Local Definition init_cond := init_cond size.

  Section SIM_FUNS.
    Context `{STGS : !stateGS Σ}.

  Definition Ist : iProp Σ :=
      (∃ (tid : Ident.t) (tids : gmap Ident.t (TView.t * nat)),
        let tids' : gmap Ident.t nat := snd <$> tids in
        SystemI.v_tid ↦src tid↑ ∗ SystemI.v_tids ↦src tids'↑ ∗
        SystemI.v_tid ↦tgt tid↑ ∗ SystemI.v_tids ↦tgt tids'↑ ∗
        tview_sys_auth tids ∗
        ([∗ map] i ↦ stid ∈ (snd <$> delete tid tids),
          (YIELD stid)))%I.

  Local Definition IstFull : iProp Σ :=
    (Ist ∗ IstEq (PFMemA.t sp))%I.

  Lemma simF_alloc :
    ⊢ ISim.sim_fun open SystemA_s SystemI_s IstFull (fid SystemHdr.alloc).
  Proof using.
    cStartFunSim. rewrite /SystemI.alloc.
    cStepsS. destruct _q as [[[tid ?] ?] ?]; iDestruct "ASM" as "[-> [-> TVS]]".
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (tid_cur tids)
      "(TID_SRC & TIDS_SRC & TID_TGT & TIDS_TGT & TA & YS)".
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
    iSplitR "EQ"; last iFrame.
    iExists tid_cur, (<[tid_cur := (V', n)]> tids).
    rewrite fmap_insert /=.
    assert (<[tid_cur := n]> (snd <$> tids) = snd <$> tids) as ->.
    { apply insert_id. rewrite lookup_fmap Hlookup //. }
    iFrame "TID_SRC TIDS_SRC TID_TGT TIDS_TGT".
    rewrite -fmap_insert /=; iFrame. rewrite delete_insert_delete.
    iSplitL "TVS TV"; eauto.
    rewrite big_sepM_insert_delete; iFrame.
  (*SLOW*)Qed.
  End SIM_FUNS.

End SystemIA.
