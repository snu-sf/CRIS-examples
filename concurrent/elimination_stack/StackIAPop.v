Require Import CRIS.common.CRIS.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.imp_system Require Import mem.MemTactics mem.MemA.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.elimination_stack Require Import StackHeader StackA StackI.
From CRIS.filter Require Import CallFilter.
From CRIS.helping Require Import HelpingTactics.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS}.

  (* Helping module being parameterized by mn *)
  Context (mn : string).
  Context (sp : specmap).

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn StackM.jobCode).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := ((StackM.t mn ★ HelpingOn) ★ MemA ★ SchI).
  Local Notation StackI := ((CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy) ★ MemA ★ SchI).
  Local Notation Ist := (IstProd (IstSB [mn] (IstHelp IstTrue ⊤)) IstEq).

  Lemma pop_simF : ISim.sim_fun open StackM StackI Ist (fid StackHdr.pop).
  Proof.
    cStartFunSim. rewrite /StackI.pop /StackM.pop /yield_iter. cStepsS; cStepsT.
    aStepS (N γs) "[%s [-> [%n #[%stackb [%stackofs [%γ [-> Hinv]]]]]]]". cStepsT. cStepsS.

    (* Coinduction starts here *)
    iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt. iIntros "[#Hinv IST] /=".
    aUnfoldT. rewrite {1}/StackI._pop. cHideT. sYields.

    (* Stack load *)
    iEval (rewrite IstHelp_nested_equiv) in "IST".
    iInv "Hinv" with "[IST]"
      as "[IST [%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]]" "close"; first by iFrame.
    mLoad.

    destruct (decide (stack_rep = Vint 0%Z)); subst.
    { (* Empty stack - terminate *)
      sYieldS. cForceS false. aUnfoldS; sYieldS. cStepsS.

      (* Atomic update *)
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      destruct l; [|ss; iPoseProof "Hlist" as "[% [% [% [% [% [% ?]]]]]]"; clarify].
      cForceS (inr _). cForcesS. iFrame.

      iMod ("close" with "[//] [Hs Hlist Hoffer H↦] IST") as ">> IST"; first (iFrame; eauto).
      iEval (rewrite -IstHelp_nested_equiv) in "IST".
      sYields. sYieldS. cStep; iFrame. iModIntro; iSplit; ss.
    }

    (* Stack nonempty *)
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".

    destruct l as [|v l]; ss; first iPoseProof "Hlist" as "%"; clarify.
    iDestruct "Hlist" as (headb headofs stackrep q0 q1) "[-> [↦v [↦next Hlist]]]".
    iDestruct "↦next" as "[↦next ↦next2]".
    iMod ("close" with "[//] [Hs Hlist H↦ ↦v ↦next2 Hoffer] IST") as ">> IST".
    { iFrame; simpl; iFrame; eauto. }
    iEval (rewrite -IstHelp_nested_equiv) in "IST".

    sYields. mLoad. sYields.

    iEval (rewrite IstHelp_nested_equiv) in "IST".
    iInv "Hinv" with "[IST]"
      as "[IST [%stack_rep1 [%offer_rep1 [%l1 [Hs [H↦ [Hlist Hoffer]]]]]]]" "close"; 
      first by iFrame.
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    mCas. iSplitL "Hcmp"; first iExact "Hcmp". iSplitR.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp". cStepsT.
    case_bool_decide; subst.
    { (* Pop success *)
      sYieldS. cForceS false. aUnfoldS. sYieldS. cStepsS.
      destruct (stack_rep1) as [[| |]|[bold ofsold]|]; inv Hcomp; case_bool_decide; ss.
      destruct l1.
      { iPoseProof "Hlist" as "%"; ss. }
      iDestruct "Hlist" as "[% [% [% [% [% [% [Hpt1 [Hpt2 Hlist]]]]]]]]". des; clarify.
      iPoseProof (mem_points_to_singleton_agree with "↦next Hpt2") as "<-".
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs ASM]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      cForceS (inr _). cForcesS. iFrame.
      iMod ("close" with "[$] [$] [$]") as ">> IST".
      iEval (rewrite -IstHelp_nested_equiv) in "IST".

      sYields. iCombine "Hval Hval2" as "Hval".
      mCmp.
      { rewrite /MemA.compare_val. case_bool_decide; ss; exfalso; naive_solver. }
      iSplitL "Hval"; first iExact "Hval". iSplitR.
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "[[% [% Hval]] _]". cStepsT.
      sYields.

      mLoad.
      iPoseProof (mem_points_to_singleton_agree with "Hval Hpt1") as "<-".
      sYields. sYieldS. cStep; iFrame. iModIntro; iSplit; ss.
    }

    (* Pop failure *)
    iMod ("close" with "[$] [$] [$]") as ">> IST".
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    sYields.
    iCombine "Hval Hval2" as "Hval".
    mCmp. iSplitL "Hval"; first iExact "Hval". iSplitR.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". cStepsT.
    assert (succ = 0%Z); last subst succ.
    { destruct stack_rep1 as [[|?|?]|[? ?]|]; inv Hcomp; ss; case_bool_decide; des; clarify; ss. }
    cStepsT. sYields.

    (* Check the offer *)
    clear dependent stack_rep1 offer_rep offer_rep1 l l1.
    iEval (rewrite IstHelp_nested_equiv) in "IST".
    iInv "Hinv" with "[IST]"
      as "[IST [%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]]" "close"; first by iFrame.
    iDestruct "Hoffer" as "[↦offer Hoffer]".
    mLoad.
    destruct (offer_rep) as [[|?|?]|[offerb offerofs]|]; try by iPoseProof ("Hoffer") as "%".
    { cStepsT. iMod ("close" with "[$] [$] IST") as ">> IST".
      iEval (rewrite -IstHelp_nested_equiv) in "IST".
      cByCoind CIH. iFrame. done. }

    iDestruct "Hoffer" as (γo γoi v' reqid) "#OfferInv".
    cStepsT. iMod ("close" with "[$] [$] IST") as ">> IST".
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    sYields.

    (* Try to take the offer *)
    iEval (rewrite IstHelp_nested_equiv) in "IST".
    iInv "OfferInv" with "[IST]" as "[IST [%offerst [↦offerst offer]]] /=" "close"; first by iFrame.
    case_decide; subst.
    { (* Helping *)
      iDestruct "offer" as "[offerv offer]".
      iAssert (emp)%I with "[]" as "E"; first done.
      mCas. iSplitL "E"; first iExact "E". iSplitR; first eauto.
      iIntros "offer↦ _". iClear "E". case_decide; last done.
      cStepsT.

      (* Help *)
      sYieldS. cForceS true. cStepsS. cInlineS. cStepsS.
      prependRetT tt. iApply (wsim_helping_help with "offer").
      iExists (S n).
      iMod ("close" with "[//]") as "[_ > close]". iModIntro.

      (* Helpee's Atomic Assume *)
      aUnfoldS. cStepsS. iApply wsim_yield_namespace_src. rewrite {3}/StackM.jobCode.
      cStepsS. clear dependent stack_rep offer_rep l.
      iInv "Hinv" with "[IST]"
        as "[IST [%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]]" "close2".
      { iFrame. solve_ndisj. }
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }

      (* Helpee's Atomic Guarantee *)
      cForcesS; first iFrame.
      iMod ("close2" with "[//]") as "[_ > close2]". cStep; iFrame.
      iIntros "#Done".

      (* My Atomic Assume *)
      cStepsS. aUnfoldS. sYieldS; cStepsS.
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }

      cForceS (inr _). cForcesS. iFrame "Hl"; cStepsS.
      iMod ("close2" with "[$] IST") as "IST".
      iMod ("close" with "[$] IST") as "IST".
      iEval (rewrite -IstHelp_nested_equiv) in "IST".
      sYields.

      iAssert (emp)%I with "[]" as "E"; first done.
      mCmp. iSplitL "E"; first iExact "E". iSplitR; first eauto.
      iIntros "_". cStepsT. sYields.

      (* Compare *)
      mLoad. sYields. sYieldS. cStep; iFrame. iModIntro; iSplit; ss.
    }

    (* Failed to take the offer - repeat the whole process! *)
    iAssert (emp)%I with "[]" as "E"; first done.
      mCas (0%Z).
    instantiate (1:=emp%I).
    iSplitL "E"; first iExact "E". iSplitR; first eauto.
    iIntros "↦offerst _". cStepsT.
    iMod ("close" with "[//] [↦offerst offer] IST") as ">> IST".
    { iExists _; ss; iFrame. case_decide; clarify. case_decide; eauto. case_decide; clarify. }
    iEval (rewrite -IstHelp_nested_equiv) in "IST".
    sYields.

    mCmp (0%Z).
    instantiate (1:=emp%I).
    iSplitL "E"; first iExact "E". iSplitR; first eauto.
    iIntros "_". cStepsT.
    sYields.

    cByCoind CIH. iFrame. done.
  (*SLOW*)Qed.
End StackIM.
