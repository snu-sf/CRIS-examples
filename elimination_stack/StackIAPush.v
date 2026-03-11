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

  Lemma Ist_help : Ist_helping mn IstFull.
  Proof.
    iIntros (??) "[% [% [% [% [[-> ->] [[[%Hdisj _] [% [[-> ->] Ha]]] ->]]]]]]".
    iModIntro; iExists _, _; iFrame; iSplit; auto.
    iIntros (?) "$ !>"; iExists _, _, _, _; repeat iSplit; eauto.
    iPureIntro. set_solver.
  Qed.
  
  Lemma push_simF : ISim.sim_fun open StackM StackI IstFull (fid StackHdr.push).
  Proof using.
    cStartFunSim. rewrite /StackI.push /StackM.push.
    rewrite /StackM.push; cStepsS. cStepsT.

    rewrite /atomic_body. cStepsS. destruct _q as [[stid mtid] [[[n vs] v] γs]].
    iDestruct "ASM" as "[TID [_ [-> #[%stackb [%stackofs [-> Hinv]]]]]]".
    cStepsT. sYieldS.
    cStepS. rewrite {3}/SchA.sp. simpl_map. cStepS.
    iApply (wsim_helping_run with "IST"); [exact Ist_help|simpl_map; s; f_equal|..].
    clear st_src; iIntros (st_src req_id) "IST Tkn".

    (* Coinduction starts here *)
    iApply wsim_reset.
    cCoind CIH g' __ with st_src st_tgt. iIntros "[#Hinv [TID [IST Help]]] /=".
    unfoldIterT. rewrite {1}/StackI._push. cStepsT.

    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    (* load *)
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [[% [% [IST ●2]]] ?]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }

    mLoadT "H↦".

    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { iLeft; iFrame. }

    (* alloc new head *)
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    iApply wsim_mem_alloc; [try by simpl_map|ss|ss|].
    iIntros (blkhead) "[↦head [↦offer _]]". cStepsT.

    (* store to new head *)
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    mStoreT "↦head".
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    mStoreT "↦offer".
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    (* try push *)
    iInv "Hinv" as "[[%stack_rep1 [%offer_rep1 [%l1 [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [[% [% [IST ●2]]] ?]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    iApply (wsim_mem_cas with "H↦ Hcmp"); [prove_inline_cond|ss|eauto| | ].
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp".
    case_bool_decide; subst.
    { (* success *)
      clear CIH.
      cStepsT.

      (* atomic update happens here: since it is valid to update stack_contents here (without any
         helps from other threads), the pusher does its own job *)
      sYieldS. cStepsS.
      iApply (wsim_helping_pend_try_run with "Help IST [-]"); [apply Ist_help|].
      cStepsS.
      iCombine "Hs ASM" gives
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      cForceS. iFrame. cStepsS. cStep.
      iFrame. iSplit; eauto.

      clear_st; iIntros (st_src st_tgt) "#Done IST". cStepsS.

      (* we updated the user-side resource, now proceed *)
      iMod ("close" with "[↦head ↦offer Hoffer Hlist H↦ Hs]") as "_".
      { iLeft. iFrame.
        destruct stack_rep, stack_rep1; inv Hcomp; try case_bool_decide; des_ifs; iFrame; eauto.
        case_bool_decide; des; clarify; iFrame; eauto.
      }

      (* comparison *)
      sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
      iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval"); [prove_inline_cond|ss|eauto| | ].
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "_". cStepsT.

      (* epilogue *)
      sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
      sYieldS. cStepsS. sYieldS.
      cForceS; iFrame "TID". iSplit; eauto.
      cStep.
      iFrame; done.
    }

    (* failure *)
    cStepsT.
    iMod ("close" with "[↦offer ↦head Hoffer Hlist H↦ Hs]") as "_".
    { iLeft. iFrame. }

    (* comparison - which leads us to offering *)
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval"); [prove_inline_cond|ss|eauto| | ].
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". cStepsT.
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    destruct (decide (succ = 0)); subst; cycle 1.
    { exfalso; destruct stack_rep1, stack_rep; inv Hcomp; des_ifs. }

    (* make an offer *)
    cStepsT. sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    iApply wsim_mem_alloc; [prove_inline_cond|ss|ss|].
    iIntros (offerb) "[↦offer [↦offerst _]]".
    cStepsT.
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    mStoreT "↦offer".
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    mStoreT "↦offerst".
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    clear dependent l l1 stack_rep stack_rep1 offer_rep offer_rep1.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [[% [% [IST ●2]]] ?]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }

    mStoreT "Hoffer↦".
    iMod (own_alloc (Excl ())) as "[%γo OfferTkn]"; ss.
    iMod (inv_alloc
      (syn_offer_inv n γo (offerb, 0%Z) req_id (stid, mtid, (n, Vptr (stackb, stackofs), v, γs)))
      _ _ _ (offerN N) with "[↦offer ↦offerst Help]") as "#Hoinv"; eauto.
    { solve_ndisj. }
    { solve_base_sl_red; iFrame; auto. }

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { iLeft. iFrame. solve_base_sl_red. iExists γo, _, _. iSplit; eauto. }
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    clear dependent l stack_rep offer_rep.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [[% [% [IST ●2]]] ?]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }
    mStoreT "Hoffer↦".

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { iLeft; iFrame. solve_base_sl_red. }
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    iInv "Hoinv" as "[%offerst [offerst↦ offer]] /=" "close".
    rewrite Z.add_0_l.
    case_decide; subst.
    { (* nobody helped*)
      iApply (wsim_mem_cas with "offerst↦"); [prove_inline_cond|ss|eauto| | | ].
      { instantiate (1:=emp%I); done. }
      { eauto. }
      case_bool_decide; ss. iIntros "Hofferst _". cStepsT.

      iMod ("close" with "[Hofferst OfferTkn]") as "_".
      { iFrame. done. }

      sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". cStepsT.

      cByCoind CIH. iDestruct "offer" as "[? ?]"; iFrame. done.
    }
    case_decide; subst.
    { (* Somebody helped *)
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "offerst↦");
        [prove_inline_cond|try prove_sb_cond|ss|..]; eauto.
      case_bool_decide; ss. iIntros "Hofferst _". cStepsT.
      iPoseProof "offer" as "#offer".

      iMod ("close" with "[Hofferst]") as "_".
      { iFrame. done. }

      sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". cStepsT.

      sYieldS. cStepsS.
      iApply (wsim_helping_done_try_run with "offer IST"); eauto using Ist_help.
      iIntros "IST".
      sYieldS. cStepsS. sYieldS. cForceS. iFrame. iSplit; eauto.
      cStep. iFrame. eauto.
    }

    case_decide; try by (iCombine "OfferTkn" "offer" gives %WF). ss.
  Unshelve. all: try exact 1%Qp.
  (*SLOW*)Qed.
End StackIM.
