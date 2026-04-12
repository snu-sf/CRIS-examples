Require Import CRIS.
Require Import PFMemHeader PFMemA base HistoryRA AtomicRA.
Require Import SystemHeader SystemA SystemTactics.
Require Import MPI MPA.

Module MPIA. Section MPIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS, _ONESHOT: !one_shotG}.
  Local Existing Instances one_shot_inG.

  Definition Ist : ist_type Σ := λ _ _, emp%I.

  Context (sp_s sp_user : specmap).
  Context (SchInSpS : (SystemA.sp sp_user ⊤) ⊆ sp_s).
  Context (HMP : MPA.sp ⊆ sp_user).

  Local Definition MA := (MPA.t sp_s ★ SystemA.t sp_user ⊤ sp_s ★ PFMemA.t sp_s).
  Local Definition MI := (MPI.t      ★ SystemA.t sp_user ⊤ sp_s ★ PFMemA.t sp_s).
  Local Definition IstFull := (IstProd (IstSB (Mod.scopes (MPA.t sp_s)) Ist) IstEq).

  Lemma mp2_spawnable : ⊢ SystemA.fspec_spawnable sp_user MPHdr.mp2 MPA.mp2_precondition.
  Proof.
    iExists MPA.mp2_spec; iSplit; [iPureIntro; by cSimpl|].
    iIntros "%P %Q [%x [-> ->]]"; iExists _, _; iSplit; [iPureIntro; exists x; split; ss|].
    unfoldPrePost. destruct x.
    iIntros (varg arg) "[$ [% [-> [% [$ [% [% $]]]]]]] /= !>"; iSplitL; eauto.
  Qed.

  Lemma simF_mp : ISim.sim_fun open MA MI IstFull entry.
  Proof using SchInSpS HMP.
    cStartFunSim. rewrite /MPI.mp /MPA.mp.
    cStepsS. iDestruct "ASM" as "[-> TV]". rewrite /MPA.mp /MPI.mp; cStepsS; cStepsT.

    iApply wsim_system_yield_ir; ss.
    { cSimpl; auto. }
    iFrame "TV IST".
    iIntros (??) "IST TV".

    (* alloc *)
    cStepsT. cInlineT. cForceT (1%positive, 0, 2, _). cForcesT. iFrame. iSplit; eauto.
    cStepsT. iDestruct "GRT" as "[-> [%loc [%V' [[-> %LE] [TV [FA ↦]]]]]]".
    rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
    cStepsT.

    (* yield *)
    iApply wsim_system_yield_ir; ss.
    { cSimpl; auto. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV". cStepsT.

    (* yield *)
    iApply wsim_system_yield_ir; ss.
    { cSimpl; auto. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV". cStepsT.

    (* write *)
    cInlineT.
    cForceT (meta0 (1%positive, 0, loc, Val.Vnum 0, Ordering.na, _))%cris.
    cForcesT. rewrite shift_0.
    iFrame "TV".
    iDestruct "↦" as "[↦flag ↦data]"; iSplitL "↦flag".
    { do 2 (iSplit; eauto). iApply own_loc_na_own_loc; done. }
    cStepsT. iDestruct "GRT" as "[-> [%V'' [[-> %HLE2] [↦flag TV]]]]".
    tview_sync HLE2.
    cStepsT.

    (* yield *)
    iApply wsim_system_yield_ir; ss.
    { cSimpl; auto. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".

    (* write *)
    cStepsT. cInlineT.
    cForceT (meta0 (1%positive, 0, loc >> 1, Val.Vnum 0, Ordering.na, _))%cris. cForcesT.
    iPoseProof (own_loc_na_own_loc with "↦data") as "$".
    iFrame "TV".
    iSplit; eauto.
    cStepsT. iDestruct "GRT" as "[-> [%V3 [[-> %Hle3] [↦data TV]]]]".
    tview_sync Hle3. cStepsT.

    (* yield *)
    iApply wsim_system_yield_ir; ss.
    { cSimpl; auto. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".

    (* spawn *)
    iMod (own_alloc Pending) as "[%γ O]"; ss.
    iMod (AtomicPtsTo_from_na loc (Val.Vnum 0) with "↦flag")
      as "[%γx [% [% [% [% [% [% [SW ↦flag]]]]]]]]".
    iMod (inv_alloc (MPA.mp_inv' 0 loc (loc >> 1) γ γx) 1 _ _ MPA.mpN with "[↦flag]") as "#I"; eauto.
    { rewrite MPA.mp_inv'_eq. solve_base_sl_red. iExists _, false, _, _, _, _, _, _.
      solve_base_sl_red; iFrame.
      iSplitL; first rewrite syn_AtomicPtsTo_red; iFrame.
      solve_base_sl_red.
    }
    iPoseProof (AtomicSWriter_AtomicSeen with "SW") as "#SN".

    (* source yield *)
    iApply wsim_system_yield_src.
    cForceS (Val.Vptr loc). cStepsS. cSimpl.

    (* spawn *)
    cForceS (1%positive, 0, MPA.mp2_precondition, V3). cForcesS.
    iFrame "TV".
    iSplitL "↦data SW".
    { iExists _; iSplit; first done.
      iExists _, _, _; iSplit; first (iPureIntro; esplits; eauto using mp2_spawnable).
      rewrite /MPA.mp2_precondition /MPA.mp_inv; iFrame "↦data SW".
      iSplitR; first iApply mp2_spawnable.
      iExists γ; iSplit; eauto. rewrite shift_0; eauto.
    }
    cStepsS. cStepsT. cCall "IST" as (ret st_src st_tgt) "IST".
    cStepsS. iDestruct "ASM" as "[% [-> [TV [-> ->]]]]".
    cStepsT. cStepsS. iApply wsim_reset. clear Hle3 H.

    cCoind CIH g' __ with st_src st_tgt V3. iIntros "[#[I SN] [FA [P [IST TV]]]]"; s.
    unfoldIterCS. cStepsS. unfoldIterCT.

    (* yield *)
    cStepsT.
    iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".

    cStepsT. cInlineT.
    iInv "I" as "INV" "ACC".
    iEval (rewrite MPA.mp_inv'_eq /MPA.mp_inv'_def; solve_base_sl_red) in "INV".
    iDestruct "INV" as "[% [%x0 [% [% [% [% [% [% [↦flag H]]]]]]]]]".
    destruct x0; cycle 1.
    { (* read 0 from flag *)
      iEval (rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def) in "↦flag".
      iDestruct "↦flag" as "[% ↦flag]".
      iEval (solve_base_sl_red) in "H"; iPoseProof "H" as "->".
      cForceT (meta1 (1%positive, 0, loc, Ordering.acqrel, _, _, _, γx, _, _, _, z1))%cris.
      cForcesT.
      iFrame "TV SN ↦flag". iSplit; et.
      cStepsT.
      iDestruct "GRT" as "[-> [% [% [% [% [% [% [%V4 [[-> %] [#SN2 [↦flag TV]]]]]]]]]]]".
      cStepsT.
      iMod ("ACC" with "[↦flag]") as "_".
      { rewrite {2}MPA.mp_inv'_eq; solve_base_sl_red; iExists _, false. repeat iExists _.
        rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def; iFrame.
        solve_base_sl_red.
      }

      iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
      iFrame "TV IST".
      clear dependent st_src st_tgt.
      iIntros (??) "IST TV".

      cStepsT. des.
      hexploit (H1 (Cell.max_ts ζ'')); first done; rewrite Cell.singleton_get.
      des_if; intros INV; inv INV.
      destruct v'; ss.
      apply Z.eqb_eq in H; subst.
      cStepsT.

      iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
      iFrame "TV IST".
      clear dependent st_src st_tgt.
      iIntros (??) "IST TV".
      cStepsT.

      iApply wsim_system_yield_src. cForceS false. cStepsS.
      cByCoind CIH. iFrame. iFrame "I".
      ss. iModIntro. iEval (rewrite H3) in "SN". done.
      Unshelve. all: try exact ⊤; try exact 1%Qp.
    }
    { (* read 1 from flag *)
      iEval (solve_base_sl_red) in "H".
      iDestruct "H" as "[% [% [% [[% %Hadd] [P2|INV]]]]]".
      { iCombine "P" "P2" gives %WF; inv WF. }
      rewrite syn_AtomicPtsTo_red.
      iEval (rewrite AtomicPtsTo_eq /AtomicPtsTo_def /view_at) in "↦flag".
      iDestruct "↦flag" as "[% ↦flag]".
      cForceT (meta1 (1%positive, 0, loc, Ordering.acqrel, _, _, _, γx, _, _, V3, z1))%cris.
      (* iPoseProof (AtomicSWriter_AtomicSeen with "SW") as "#SN". *)
      cForcesT. iFrame "TV SN ↦flag". iSplit; eauto.
      cStepsT.
      iDestruct "GRT" as "[-> [% [% [% [% [% [% [% [[-> %Hres] [#SN2 [↦flag TV]]]]]]]]]]]".
      destruct Hres as [Hval [Hcell1 [Hcell2 [Hget [Hvle Hvle2]]]]].
      hexploit (Hcell2 (Cell.max_ts ζ'')); eauto.
      erewrite Cell.add_o; eauto; des_if.
      { (* read 1 *)
        subst. intros INV; inv INV.
        (* iClear "CIH". *)
        destruct v'; ss. apply Z.eqb_eq in Hval; subst.
        cStepsT.
        iMod ("ACC" with "[↦flag P]") as "_".
        { rewrite MPA.mp_inv'_eq; solve_base_sl_red.
          iExists _, true; repeat iExists _.
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def; iFrame.
          solve_base_sl_red; iFrame "P"; auto.
        }

        (* yield *)
        iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        cStepsT.

        (* yield *)
        iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        cStepsT.

        (* yield *)
        iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        cStepsT.

        (* non-atomic load here *)
        cInlineT.
        cForceT (meta0 (_, _, _, _, _, _, _))%cris.
        iEval (rewrite syn_own_loc_na_red) in "INV".
        assert (Hawk : Ordering.le Ordering.acqrel Ordering.acqrel) by refl. cForcesT.
        rewrite Hvle2 Hawk Hvle.
        iFrame "TV INV". iSplit; eauto.

        cStepsT. iDestruct "GRT" as "[-> [% [% [[-> %Hval'] [↦data TV]]]]]".

        cStepsT.
        iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        cStepsT.

        destruct v'; ss. eapply Z.eqb_eq in Hval'; subst.
        cStepsT.

        iApply wsim_system_yield_src. cForceS true; cStepsS.
        cForcesS. iSplit; eauto.
        cStep.
        iSplit; eauto.
      }
      { (* read 0 *)
        rewrite Cell.singleton_get; des_if; intros INV; inv INV.
        destruct v'; ss. eapply Z.eqb_eq in Hval; subst.
        cStepsT.

        (* close invariant *)
        iMod ("ACC" with "[↦flag INV]") as "_".
        { iClear "I". rewrite MPA.mp_inv'_eq. iEval solve_base_sl_red. iExists _, true.
          do 6 iExists _.
          rewrite syn_AtomicPtsTo_red AtomicPtsTo_eq /AtomicPtsTo_def; iFrame.
          iEval solve_base_sl_red. iFrame "INV"; eauto.
        }

        (* yield *)
        iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        cStepsT.

        (* yield *)
        iApply wsim_system_yield_ir; ss. { cSimpl; auto. }
        iFrame "TV IST".
        clear dependent st_src st_tgt.
        iIntros (??) "IST TV".
        cStepsT.

        iApply wsim_system_yield_src. cForceS false. cStepsS.
        cByCoind CIH. iFrame. iFrame "I".
        iEval (rewrite Hvle) in "SN"; s; iModIntro; done.
      }
    }
  Unshelve. all: try exact 1%Qp; try exact ⊤.
  (*SLOW*)Qed.

  Lemma simF_mp2 : ISim.sim_fun open MA MI IstFull (fid MPHdr.mp2).
  Proof using SchInSpS HMP.
    cStartFunSim. rewrite /sfunU /sfunN /MPI.mp2.
    cStepsS. destruct _q as [tid stid].
    iDestruct "ASM" as "[%va [-> [%sa [%V [-> [PRE TV]]]]]]".
    iDestruct "PRE" as "[%loc [%γ [%γx [%V0 [%fd [%td [% [% [[-> ->] [#I [↦data ⊒]]]]]]]]]]]".
    cStepsS.

    rewrite /MPA.mp2. cStepsS.
    cStepsT.
    rewrite /MPI.mp2.

    (* yield *)
    iApply wsim_system_yield_ir; ss. { cSimpl; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    cStepsT.

    (* yield *)
    iApply wsim_system_yield_ir; ss. { cSimpl; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    cStepsT.

    (* write to data *)
    cInlineT.
    cForceT (meta0 (_, _, _, _, _, _))%cris.
    cForcesT.
    iPoseProof (own_loc_na_own_loc with "↦data") as "↦data".
    iFrame "TV ↦data". iSplit; eauto.
    cStepsT. iDestruct "GRT" as "[-> [%V2 [[-> %Hle] [↦data TV]]]]".
    cStepsT.

    (* yield *)
    iApply wsim_system_yield_ir; ss. { cSimpl; ss. }
    iFrame "TV IST".
    clear dependent st_src st_tgt.
    iIntros (??) "IST TV".
    cStepsT.

    (* open invariant *)
    iInv "I" as "INV" "ACC".
    iEval (rewrite MPA.mp_inv'_eq /MPA.mp_inv'_def; solve_base_sl_red) in "INV".
    iDestruct "INV" as "[% [%x0 [% [% [% [% [% [% [↦flag H]]]]]]]]]".
    rewrite syn_AtomicPtsTo_red.
    rewrite shift_0; iPoseProof (AtomicPtsTo_SWriter_agree with "[$] [$]") as "->".

    cInlineT. cStepsT.
    iEval (rewrite AtomicPtsTo_eq /AtomicPtsTo_def /view_at) in "↦flag".
    iDestruct "↦flag" as "[% ↦flag]".
    cForceT (meta1 (tid, stid, loc, Val.Vnum 1, Ordering.acqrel, V2, γx, _, _, _, _, _, _, _))%cris.
    cForcesT.
    iFrame "↦flag". iSplitL "⊒ TV"; eauto.
    { iSplit; eauto. iSplit; eauto. iFrame. tview_sync Hle.
      iPoseProof (AtomicSWriter_AtomicSeen with "⊒") as "#sn"; iSplit; eauto.
      rewrite AtomicSWriter_eq /AtomicSWriter_def /view_at /=; iDestruct "⊒" as "[? [? ?]]"; iFrame.
    }
    Unshelve. all: try exact 1%Qp.
    cStepsT.

    iDestruct "GRT" as "[-> [% [% [% [% [% [% [[-> [%Htime %Hres]] [sn [at [sy [swX tv]]]]]]]]]]]]".
    destruct (Ordering.le _ _) eqn : Heqb in Hres; ss; subst; clear Heqb.
    rewrite Cell.max_ts_singleton in Htime.
    des; subst. cStepsT.
    iMod ("ACC" with "[↦data swX]") as "_".
    { rewrite MPA.mp_inv'_eq.
      iEval solve_base_sl_red; iExists _, true; repeat iExists _.
      rewrite syn_AtomicPtsTo_red; iSplitL "swX".
      { rewrite AtomicPtsTo_eq /AtomicPtsTo_def /view_at; iExists t; iFrame. }
      solve_base_sl_red; repeat iExists _.
      iSplitR "↦data".
      { iPureIntro. split; eauto. }
      iRight; rewrite syn_own_loc_na_red.
      iApply (own_loc_mon_pred_gen with "↦data"); eauto; try exact 1%Qp.
      apply View.join_l.
    }

    iApply wsim_system_yield_ir; ss. { cSimpl; ss. }
    iFrame "tv IST". clear dependent st_src st_tgt; iIntros (st_src st_tgt) "IST TID".
    cStepsT.

    iApply (wsim_system_yield_src with "[-]"). cStepsS. cForcesS.
    iFrame. iSplitR; [eauto|]. cStep. iFrame. done. 
  Unshelve. all: try exact ⊤.
  Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    cStartModSim.
    { eapply simF_mp2. }
    { eapply simF_mp. }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.
End MPIA.
Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS, _ONESHOT: !one_shotG}.

  Definition ctxr (sp_s sp_user : specmap) :
    (SystemA.sp sp_user ⊤) ⊆ sp_s →
    MPA.sp ⊆ sp_user →
    ctx_refines
      ((MPI.t      ★ SystemA.t sp_user ⊤ sp_s ★ PFMemA.t sp_s), True%I)
      ((MPA.t sp_s ★ SystemA.t sp_user ⊤ sp_s ★ PFMemA.t sp_s), emp%I).
  Proof using. intros ??; eapply main_adequacy, sim; eauto. Qed.
End ctxr.
End MPIA.
