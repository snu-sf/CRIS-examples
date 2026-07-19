Require Import CRIS.common.CRIS.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.imp_system Require Import mem.MemTactics mem.MemA.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.elimination_stack Require Import StackHeader StackA StackI.
From CRIS.helping Require Import HelpingTactics HelpingFacts.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS}.

  (* Helping module being parameterized by mn *)
  Context (mn : string).

  (* Stack module being masked for eliminating the helping module *)
  Context (sp : specmap).

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn StackM.jobCode).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := ((StackM.t mn ★ HelpingOn) ★ MemA ★ SchI).
  Local Notation StackI := ((CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy) ★ MemA ★ SchI).

  Lemma push_simF : ISim.sim_fun open StackM StackI (IstHelp mn ⊤) (fid StackHdr.push).
  Proof.
    cStartFunSim. rewrite /StackI.push /StackM.push. cStepsS; cStepsT.
    aStepS (N [v γs]) "[%s [-> [%n #[%stackb [%stackofs [%γh [-> Hinv]]]]]]]".

    cStepsS; cStepsT.
    iApply (wsim_helping_run with "IST"); [simpl_map; s; f_equal|..].
    clear_st; iIntros (st_src req_id) "IST Tkn". cStepsS.

    (* Coinduction starts here *)
    iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt. iIntros "[#Hinv [IST Help]] /=".
    aUnfoldT. rewrite {1}/StackI._push. cStepsT. cHideT. sYields.

    (* load *)
    iInv "Hinv" with "[IST]"
      as "[IST [%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]]" "close"; first by iFrame.
    mLoad.
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    iMod ("close" with "[//] [Hs Hlist H↦ Hoffer] [$]") as "> > IST"; first by iFrame.

    (* alloc new head *)
    sYields. mAllocT as (blkhead) "[↦head [↦offer _]]". sYields.

    (* store to new head *)
    mStore. sYields. mStore. sYields.

    (* try push *)
    iInv "Hinv" with "[IST]"
      as "[IST [%stack_rep1 [%offer_rep1 [%l1 [Hs [H↦ [Hlist Hoffer]]]]]]]" "close";
      first by iFrame.
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    cShowT. mCas. iSplitL "Hcmp"; first iExact "Hcmp". iSplitR.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp". cStepsT. cHideT.
    case_bool_decide; subst.
    { (* success *)
      clear CIH.

      (* atomic update happens here: since it is valid to update stack_contents here (without any
         helps from other threads), the pusher does its own job *)
      sYieldS. prependRetT tt.
      iApply (wsim_helping_pend_try_run with "Help IST [-]").
      clear_st. iIntros (st_src2) "IST".
      aUnfoldS. rewrite {3}/StackM.jobCode. cNormS. sYieldS. cStepsS.
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      cForcesS. iFrame. cStep. iFrame.

      clear_st. iIntros (st_src1 st_tgt1) "#Done IST". cStepsS.

      (* we updated the user-side resource, now proceed *)
      iMod ("close" with "[//] [↦head ↦offer Hoffer Hlist H↦ Hs] [$]") as "> > IST".
      { destruct stack_rep, stack_rep1; inv Hcomp; try case_bool_decide; des_ifs; iFrame; eauto.
        case_bool_decide; des; clarify; iFrame; eauto.
      }

      (* comparison *)
      cHideT. sYields.
      iCombine "Hval" "Hval2" as "Hval".
      mCmp. iSplitL "Hval"; first iExact "Hval". iSplitR.
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "_". cStepsT.

      (* epilogue *)
      sYields. sYieldS. cStep; iFrame. done.
    }

    (* failure *)
    iMod ("close" with "[//] [$] [$]") as "> > IST".

    (* comparison - which leads us to offering *)
    sYields.
    iCombine "Hval" "Hval2" as "Hval".
    mCmp. iSplitL "Hval"; first iExact "Hval". iSplitR.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". cStepsT. sYields.
    destruct (decide (succ = 0)); subst; cycle 1.
    { exfalso; destruct stack_rep1, stack_rep; inv Hcomp; des_ifs. }

    (* make an offer *)
    cStepsT. sYields. iClear "↦head ↦offer".
    mAllocT as (offerb) "[↦offer [↦offerst _]]". sYields.
    mStore. sYields. mStore. sYields.

    clear dependent l l1 stack_rep stack_rep1 offer_rep offer_rep1.
    iInv "Hinv" with "[IST]"
      as "[IST [%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer _]]]]]]]]" "close";
      first by iFrame.
    mStore.
    iMod (own_alloc (Excl ())) as "[%γo OfferTkn]"; ss.
    iMod (hinv_alloc (syn_offer_inv N n γo (offerb, 0%Z) req_id v _)
      _ _ (offerN N) with "[↦offer ↦offerst Help]") as "[%γ #Hoinv]"; eauto.
    { solve_ndisj. }
    { rewrite sl_red; iFrame; eauto. }

    iMod ("close" with "[//] [$] IST") as "> > IST".
    sYields.

    clear dependent l stack_rep offer_rep.
    iInv "Hinv" with "[IST]"
      as "[IST [%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer _]]]]]]]]" "close";
      first by iFrame.
    mStore.

    iMod ("close" with "[//] [$] [$]") as "> > IST". sYields.
    iInv "Hoinv" with "[IST]" as "[IST [%offerst [offerst↦ offer]]]" "close"; first by iFrame.
    rewrite Z.add_0_l.
    case_decide; subst.
    { (* nobody helped - try again *)
      mCas. instantiate (1:=emp%I). iSplitR; first done. iSplitR.
      { eauto. }
      case_bool_decide; ss. iIntros "Hofferst _". cStepsT.

      iMod ("close" with "[//] [$] [$]") as "> > IST". sYields.
      iAssert (emp)%I as "E"; first done.
      mCmp. iSplitL "E"; first iExact "E". iSplitR; first eauto.
      iIntros "_". cStepsT.

      cByCoind CIH. iFrame "∗#". iDestruct "offer" as "[? ?]"; iFrame.
    }
    case_decide; subst.
    { (* Somebody helped *)
      mCas. instantiate (1:=emp%I). iSplitR; first done. iSplitR; first eauto.
      case_bool_decide; ss. iIntros "Hofferst _". cStepsT.
      iPoseProof "offer" as "#offer".

      iMod ("close" with "[//] [$] [$]") as ">>IST".
      sYields. iAssert (emp)%I as "E"; first done.
      mCmp. iSplitL "E"; first iExact "E". iSplitR; first eauto.
      iIntros "_". cStepsT.

      sYieldS. iApply (wsim_HelpDone_try_run with "offer IST"). iIntros "IST".
      cStepsS. sYieldS. cStep; iFrame. done.
    }

    case_decide; try by (iCombine "OfferTkn" "offer" gives %WF). done.
  Unshelve. all: try exact 1%Qp.
  (*SLOW*)Qed.
End StackIM.
