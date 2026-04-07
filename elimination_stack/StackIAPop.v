Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI.
Require Import HelpingTactics HelpingFacts.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !stackG StackM.jobID StackM.retID}.
  Local Existing Instances stack_helpingG.

  (* Helping module being parameterized by mn *)
  Context (mn : string).

  (* Stack module being masked for eliminating the helping module *)
  Context (N : namespace) (sp sp_user : specmap).

  Definition init_cond : iProp Σ := helping_auth 1 ∅%I.

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn StackM.jobCode (SchA.sp ∅ (↑N))).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := ((StackM.t mn N (SchA.sp ∅ (↑N)) ★ HelpingOn) ★ MemA ★ SchI).
  Local Notation StackI := ((CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy) ★ MemA ★ SchI).
  Local Notation IstFull := (IstProd (IstSB [mn] (IstHelp mn)) IstEq).

  Lemma pop_simF : ISim.sim_fun open StackM StackI IstFull (fid StackHdr.pop).
  Proof using.
    cStartFunSim. rewrite /StackI.pop /StackM.pop /yield_iter. cStepsS; cStepsT.
    aStepS. iIntros (mtid stid γs) "TID [%v [-> [%n #Hstack]]]".
    iDestruct "Hstack" as "#[%stackb [%stackofs [-> Hinv]]]". cStepsT. cStepsS.

    (* Coinduction starts here *)
    iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt. iIntros "[#Hinv [IST TID]] /=".
    aUnfoldT. rewrite {1}/StackI._pop. cStepsT.
    sYieldIR "IST" "TID". sYieldIR "IST" "TID".

    (* Stack load *)
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [[% [% [IST ●2]]] ?]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    mLoadT "H↦".

    destruct (decide (stack_rep = Vint 0%Z)); subst.
    { (* Empty stack - terminate *)
      sYieldS. cForceS false. cStepsS. aUnfoldS; sYieldS. cStepsS.

      (* Atomic update *)
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      destruct l; [|ss; iPoseProof "Hlist" as "[% [% [% [% [% [% ?]]]]]]"; clarify].
      cForceS (inr _). cForcesS. iFrame.

      iMod ("close" with "[Hs Hlist Hoffer H↦]") as "_".
      { iLeft. iFrame. et. }
      sYieldIR "IST" "TID".
      sYieldS. cStep; iFrame. iModIntro; iSplit; ss.
    }
    (* Stack nonempty *)
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".

    destruct l as [|v l]; ss; first iPoseProof "Hlist" as "%"; clarify.
    iDestruct "Hlist" as (headb headofs stackrep q0 q1) "[-> [↦v [↦next Hlist]]]".
    iDestruct "↦next" as "[↦next ↦next2]".
    iMod ("close" with "[Hs Hlist H↦ ↦v ↦next2 Hoffer]") as "_".
    { iLeft. iFrame. iExists _, _, _, _; iFrame; eauto. }

    sYieldIR "IST" "TID". sYieldIR "IST" "TID".
    mLoadT "↦next". sYieldIR "IST" "TID".

    iInv "Hinv" as "[[%stack_rep' [%offer_rep' [%l' [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [[% [% [IST ●2]]] ?]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    iApply (wsim_mem_cas with "H↦ Hcmp");
      [prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp". cStepsT.
    case_bool_decide; subst.
    { (* Pop success *)
      sYieldS. cForceS false. cStepS. aUnfoldS. sYieldS. cStepsS.
      destruct (stack_rep') as [[| |]|[bold ofsold]|]; inv Hcomp; case_bool_decide; ss.
      destruct l'.
      { iPoseProof "Hlist" as "%"; ss. }
      iDestruct "Hlist" as "[% [% [% [% [% [% [Hpt1 [Hpt2 Hlist]]]]]]]]". des; clarify.
      iPoseProof (mem_points_to_singleton_agree with "↦next Hpt2") as "<-".
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs ASM]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      cForceS (inr _). cForcesS. iFrame.
      iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
      { iLeft. iFrame. }
      sYieldIR "IST" "TID".

      iCombine "Hval Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval"); [try prove_inline_cond|try prove_sb_cond|ss|..]; eauto.
      { case_bool_decide; ss; exfalso; naive_solver. }
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "[[% [% Hval]] _]". cStepsT.
      sYieldIR "IST" "TID".

      mLoadT "Hval".
      iPoseProof (mem_points_to_singleton_agree with "Hval Hpt1") as "<-".
      sYieldIR "IST" "TID".
      sYieldS. cStep; iFrame. iModIntro; iSplit; ss.
    }

    (* Pop failure *)
    iMod ("close" with "[↦next Hs Hoffer Hlist H↦]") as "_".
    { iLeft. iFrame. }
    sYieldIR "IST" "TID". cStepsT.
    iCombine "Hval Hval2" as "Hval".
    iApply (wsim_mem_cmp with "Hval");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". cStepsT.
    assert (succ = 0%Z); last subst succ.
    { destruct stack_rep' as [[|?|?]|[? ?]|]; inv Hcomp; ss; case_bool_decide; des; clarify; ss. }
    cStepsT.
    sYieldIR "IST" "TID".

    (* Check the offer *)
    clear dependent stack_rep' offer_rep offer_rep' l  l'.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [[% [% [IST ●2]]] ?]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iDestruct "Hoffer" as "[↦offer Hoffer]".
    mLoadT "↦offer".
    rewrite /syn_is_offer; destruct (offer_rep) as [[|?|?]|[offerb offerofs]|]; solve_base_sl_red;
      try iPoseProof ("Hoffer") as "%".
    { cStepsT. iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
      { iLeft; iFrame. solve_base_sl_red. }
      cByCoind CIH. iFrame. done.
    }
    iDestruct "Hoffer" as (γo [v' γs'] reqid) "[OfferInv <-]".
    iPoseProof ("OfferInv") as "#OfferInv".

    cStepsT.
    iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
    { iLeft; iFrame. solve_base_sl_red. repeat iExists _; iSplit; eauto. }
    sYieldIR "IST" "TID".

    (* Try to take the offer *)
    iInv "OfferInv" as "[%offerst [↦offerst offer]] /=" "close".

    case_decide; subst.
    { (* Helping *)
      iDestruct "offer" as "[offerv offer]".
      iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cas with "↦offerst E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "offer↦ _". iClear "E". case_decide; last done.
      cStepsT.

      (* Help *)
      sYieldS. cForceS true. cStepsS.
      cInlineS. cStepsS.
      iDestruct "IST" as "[% [% [% [% [[-> ->] [[% [% [[-> ->] ●Help]]] IST]]]]]]".
      iPoseProof (helping_auth_token with "●Help offer") as "%Hreq".
      iMod (helping_auth_commit with "●Help offer") as "[●offer #◯offer]".
      iMod ("close" with "[offer↦ ◯offer]") as "_".
      { iExists 1; iFrame; case_decide; ss. }
      rewrite /HelpingOn.help. simpl_map. cForceS reqid.
      cForceS (stid, mtid, tt). cForcesS. iFrame. iSplit; first eauto. cStepsS.
      destruct _q as [[stid1 mtid1] []]. iDestruct "ASM" as "[TID [_ ->]]".

      (* Helpee's Atomic Assume *)
      rewrite /HelpingOn.try_run. cStepsS. rewrite Hreq /= /StackM.jobCode.
      cStepsS. clear dependent stack_rep offer_rep l.
      iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "Close";
        cycle 1.
      { iExFalso. iCombine "●" "●offer" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss. }
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }

      (* Helpee's Atomic Guarantee *)
      cForcesS; iFrame. cStepsS.

      (* My Atomic Assume *)
      iPoseProof (helping_auth_split (1/2) with "●offer") as "[●offer ●reclaim]"; ss.
      iMod ("Close" with "[●offer]") as "_".
      { iRight; iFrame. }
      cForcesS. iFrame; iSplit; eauto. cStepsS. aUnfoldS. sYieldS; cStepsS.
      iDestruct "ASM" as "[TID [_ ->]]".
      iCombine "Hs ASM'" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete. ss.
      iMod (own_update_2 with "Hs ASM'") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }

      cForceS (inr _). cForcesS. iFrame "Hl"; cStepsS.
      iInv "Hinv" as "[[% [% [% [Hs' _]]]]|[% ●]]" "close".
      { iExFalso. iCombine "Hs" "Hs'" gives %WF; inv WF. }
      iPoseProof ("●reclaim" with "●") as "●".
      iMod ("close" with "[- IST TID ● offerv]") as "_".
      { iLeft; iFrame. }
      cIst "IST" with "[● IST]".
      { iExists _, _, _, _; iFrame. iSplit; eauto. iPureIntro; esplits; eauto; set_solver. }
      sYieldIR "IST" "TID".

      iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". cStepsT.
      sYieldIR "IST" "TID". sYieldIR "IST" "TID".

      (* Compare *)
      mLoadT "offerv".
      sYieldIR "IST" "TID".
      sYieldS. cStep; iFrame. iModIntro; iSplit; ss.
    }

    (* Failed to take the offer - repeat the whole process! *)
    iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cas with "↦offerst E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). case_bool_decide; ss; des_ifs; ss. }
    iIntros "↦offerst _". cStepsT.
    iMod ("close" with "[↦offerst offer]") as "_".
    { iExists _; ss; iFrame. case_decide; clarify. case_decide; eauto. case_decide; clarify. }
    sYieldIR "IST" "TID".

    iApply (wsim_mem_cmp with "E");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). case_bool_decide; clarify; des_ifs; ss. }
    iIntros "_". cStepsT.
    sYieldIR "IST" "TID".

    cByCoind CIH. iFrame. done.
  (*SLOW*)Qed.
End StackIM.
