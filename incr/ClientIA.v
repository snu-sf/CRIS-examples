Require Import CRIS Atomic atomic.
Require Export IncrHeader ClientI ClientA IncrA SchA MemA.
Require Import SchTactics MemTactics.
From iris Require Import frac_auth numbers.

(* Proof of refinement between ClientA.t and ClientI.t *)
Module ClientIA. Section ClientIA.
  Import ClientA.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS, !schGS, !incrG}.

  Context (N : namespace).
  Context (sp_user sp : specmap).
  Context (Hclient : ClientA.sp N ⊆ sp_user).
  Context (Hsch : SchA.sp sp_user (↑N) ⊆ sp).

  Local Definition IstFull := (IstProd (IstSB (ClientA.t N sp).(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (ClientA.t N sp ★ MemA.t sp).
  Local Definition MI := ((ClientI.t ★ IncrA.t (N.@"a")) ★ MemA.t sp).

  Lemma f_spawnable γ v bofs :
    ⊢ SchA.fn_spawnable sp_user (ClientHdr.thread)
      (λ varg arg,
        ⌜varg = arg ∧ varg = ([Vptr bofs]↑↑)⌝
        ∗ counter γ (1/2) v
        ∗ incr_inv 0 N γ bofs)%I
      (λ vret ret,
        existT 0 ((⌜vret = ret ∧ vret = tt↑↑⌝ ∗ counter_syn γ (1/2) (v + 2))%SAT)).
  Proof using Hclient.
    iExists _; iSplitL.
    { simpl_sp. eauto. }
    iApply SchA.fspec_sch_spawnable; first done.
    iIntros "%P1 %Q1 [% [-> ->]]"; iExists _, _; iSplit; first (iPureIntro).
    { exists (bofs, v, γ); split; ss. }
    unfoldPrePost.
    iIntros (varg arg) "[%va [%sarg [[% %] [% $]]]]"; des; clarify.
    iIntros "!>"; iSplit; first done; iIntros "%% [[-> ->] ?] !>"; iExists _, _; iSplit; eauto.
    solve_base_sl_red; iSplit; done.
  Qed.

  Lemma incr_simF : ISim.sim_fun open MA MI IstFull (fid ClientHdr.thread).
  Proof using Hsch Hclient.
    cStartFunSim.

    cStepsS. destruct _q as [[stid mtid] [[[blk ofs] v] γ]]. rename _q0 into varg.
    iDestruct "ASM" as "[TID [[-> ->] [C #INV]]]".

    cStepsS. cStepsT. rewrite /sfunU /sfunN /incr /ClientI.thread /=; cStepsT. cStepsS.

    sYieldIR "IST" "TID".

    (* tgt inline - faa *)
    cInlineT. cStepsT. rewrite /IncrA.incr. aForceT with "IST TID".
    iExists 1. iAuIntro. iInv "INV" as "[%x [↦ CA]]".
    iAaccIntro with "↦". iSplit.
    { iIntros "$"; by iFrame. }
    iIntros (ret_t) "↦ !>"; iExists (tt↑); iSplitR; first done.
    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; iFrame.
    clear_st. iIntros "!>" (st_src st_tgt) "IST TID ->". cStepsT. sYieldIR "IST" "TID".

    (* tgt inline - faa *)
    cInlineT. cStepsT. rewrite /IncrA.incr. aForceT with "IST TID".
    iExists 1. iAuIntro. clear x. iInv "INV" as "[%x [↦ CA]]".
    iAaccIntro with "↦". iSplit.
    { iIntros "$"; by iFrame. }
    iIntros (ret_t) "↦ !>"; iExists (tt↑); iSplitR; first done.
    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; iFrame.
    clear_st. iIntros "!>" (st_src st_tgt) "IST TID ->". cStepsT. sYieldIR "IST" "TID".

    sYieldS. cForcesS. iFrame. iSplitL "C".
    { iFrame. replace (v + 1 + 1)%Z with (v + 2)%Z by lia. iFrame. eauto. }
    cStep; iFrame; done.
(*SLOW*)Qed.

  Lemma main_simF : ISim.sim_fun open MA MI IstFull entry.
  Proof using Hsch Hclient.
    cStartFunSim.

    cStepsS. destruct _q as [[stid mtid] []]; s.
    iDestruct "ASM" as "[TID ->]".
    rewrite /main /ClientI.main.

    (* src/tgt yield *)
    cStepsT. cStepsS.
    sYieldIR "IST" "TID".

    (* tgt alloc *)
    mAllocT as (blk) "[map _]". cStepsT.
    sYieldIR "IST" "TID".
    sYieldIR "IST" "TID".

    (* tgt store *)
    mStoreT "map". sYieldIR "IST" "TID".
    sYieldS. cForceS (Vptr (blk, 0%Z)). cStepsS. sYieldS. cStepsS.

    (* spawn *)
    iMod (own_alloc ((●F 0%Z ⋅ ◯F{1} 0%Z))) as "[%γc [A F]]".
    { apply frac_auth_valid; ss. }
    iMod (inv_alloc (syn_ccounter γc (blk, 0%Z)) _ _ _ (N.@"client") with "[map A]") as "#I"; eauto.
    { apply nclose_subseteq. }
    { solve_base_sl_red; iFrame. }
    iPoseProof (counter_op with "[F]") as "[F1 F2]".
    { rewrite -Qp.half_half -{2}(Z.add_0_r 0%Z). iApply "F". }

    (* src/tgt spawns *)
    rewrite /Sch.spawn; cStepsT; cStepsS. simpl_sp.
    cForceS (_, _); cForcesS; iSplitL "F1".
    { iExists _, _, _; iSplit; eauto.
      iSplitR; first iApply f_spawnable.
      iFrame "#∗"; eauto.
    }
    cStepsS. cCall "IST" as (ret ??) "IST".
    cStepsS. iDestruct "ASM" as "[% [[-> ->] Handle]]". cStepsS. cStepsT.
    sYieldIR "IST" "TID".
    sYieldS.

    rewrite /Sch.spawn; cStepsT; cStepsS. simpl_sp.
    cForceS (_, _); cForcesS; iSplitL "F2".
    { iExists _, _, _; iSplit; eauto.
      iSplitR; first iApply f_spawnable.
      iFrame; eauto.
    }
    cStepsS. cCall "IST" as (ret ??) "IST".
    cStepsS. iDestruct "ASM" as "[% [[-> ->] Handle2]]". cStepsS. cStepsT.
    sYieldIR "IST" "TID".
    sYieldS.

    rewrite /Sch.join; cStepsT; cStepsS. simpl_sp.
    cForceS (_, _, _); cForcesS. iFrame "TID Handle"; iSplit; [eauto|]. cStepsS.
    cCall "IST" as (ret ??) "IST".
    cStepsS. iDestruct "ASM" as "[TID [% [% [[-> ->] ASM]]]]".
    solve_base_sl_red. iDestruct "ASM" as "[[-> ->] Q]".
    cStepsS. cStepsT.
    sYieldIR "IST" "TID".
    sYieldS.

    rewrite /Sch.join; cStepsT; cStepsS. simpl_sp.
    cForceS (_, _, _); cForcesS. iFrame "TID Handle2"; iSplit; [eauto|]. cStepsS.
    cCall "IST" as (ret ??) "IST".
    cStepsS. iDestruct "ASM" as "[TID [% [% [[-> ->] ASM]]]]".
    solve_base_sl_red. iDestruct "ASM" as "[[-> ->] Q2]".
    cStepsS. cStepsT.
    sYieldIR "IST" "TID".

    iInv "I" as "[%x [PT C]]" "INVA".
    iCombine "C Q Q2" as "C" gives %[_ WF%frac_auth_agree]. inv WF; ss.
    iDestruct "C" as "[CA CF]".

    cStepsT. mLoadT "PT".

    iMod ("INVA" with "[CA PT]") as "_"; first solve_base_sl_red; iFrame.

    sYieldIR "IST" "TID". sYieldIR "IST" "TID".
    sYieldS; cStepsS. replace (0 + 2 + (0 + 2))%Z with 4%Z by lia.

    cStep.
    cStepsS. cStepsT.
    sYieldIR "IST" "TID".
    sYieldS. cStepsS. cForcesS. iFrame "TID"; iSplit; eauto.
    cStep. iFrame. done.
(*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof using Hsch Hclient.
    cStartModSim.
    { eapply incr_simF. }
    { eapply main_simF. }
    { iIntros "_"; iExists _, _, _, _; iSplit; eauto. }
  Qed.
End ClientIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !incrG}.

  Definition ctxr (N : namespace) (sp_user sp : specmap) :
    ClientA.sp N ⊆ sp_user →
    (SchA.sp sp_user (↑N)) ⊆ sp →
    ctx_refines
      (ClientI.t      ★ IncrA.t (N.@"a") ★ (MemA.t sp), emp%I)
      (ClientA.t N sp ★ MemA.t sp, emp%I).
  Proof using.
    etrans. { do 2 ctxr_rotate. ctxr_refl. }
    eset (GRP := ClientI.t ★ _).
    etrans. { ctxr_rotate. ctxr_refl. }
    do 2 ctxr_rotate.
    eapply main_adequacy, sim; eauto.
  Qed.
End ctxr. End ClientIA.
