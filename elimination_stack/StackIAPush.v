Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI.
Require Import HelpingTactics HelpingFacts.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS, _CONC: !concGS, !stackG StackM.jobID StackM.retID}.
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
  Local Notation StackM := (SchI ★ MemA ★ StackM.t mn N ((SchA.sp ∅ (↑N))) ★ HelpingOn).
  Local Notation StackI := (SchI ★ MemA ★ CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy).

  Local Notation IstFull := (HelpingTactics.IstFull StackM.jobID StackM.retID mn).

  Lemma push_simF : ISim.sim_fun open StackM StackI IstFull (Some StackHdr.push).
  Proof using.
    iStartSim.
    rewrite /StackM.push; steps_l. steps_r.

    rewrite /atomic_body. steps_l. destruct _q as [[stid mtid] [[[n vs] v] γs]].
    iDestruct "ASM" as "[TID [_ [-> #[%stackb [%stackofs [-> Hinv]]]]]]".
    steps_r. sch_yield_l.
    step_l. rewrite {3}/SchA.sp. simpl_map. step_l.
    iApply (wsim_helping_run with "IST"); [|].
    { simpl_map. rewrite /SB.sandbox_body. s. refl. }
    clear st_src st_tgt; iIntros (st_src st_tgt req_id) "IST Tkn".

    (* Coinduction starts here *)
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#Hinv [TID [IST Help]]] /=".
    destruct_quant CIH.

    unfold_iter_r. rewrite {1}/StackI._push. steps_r.

    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* load *)
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }

    load_r "H↦".

    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".
    iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
    { iLeft; iFrame. }

    (* alloc new head *)
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    iApply wsim_mem_alloc; [try by simpl_map|ss|ss|].
    iIntros (blkhead) "[↦head [↦offer _]]". steps_r.

    (* store to new head *)
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    store_r "↦head".
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    store_r "↦offer".
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* try push *)
    iInv "Hinv" as "[[%stack_rep1 [%offer_rep1 [%l1 [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
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
      steps_r.

      (* atomic update happens here: since it is valid to update stack_contents here (without any
         helps from other threads), the pusher does its own job *)
      sch_yield_l. norm_l.
      iApply (wsim_helping_pend_try_run with "Help IST [-]").
      steps_l.
      iCombine "Hs ASM" gives
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l. iFrame. steps_l. step.
      iFrame. iSplit; eauto.

      clear_st; iIntros (st_src st_tgt) "#Done IST". steps_l.

      (* we updated the user-side resource, now proceed *)
      iMod ("close" with "[↦head ↦offer Hoffer Hlist H↦ Hs]") as "_".
      { iLeft. iFrame.
        destruct stack_rep, stack_rep1; inv Hcomp; try case_bool_decide; des_ifs; iFrame; eauto.
        case_bool_decide; des; clarify; iFrame; eauto.
      }

      (* comparison *)
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval"); [prove_inline_cond|ss|eauto| | ].
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "_". steps_r.

      (* epilogue *)
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      sch_yield_l. steps_l. sch_yield_l.
      force_l; iFrame "TID". iSplit; eauto.
      step.
      iFrame; done.
    }

    (* failure *)
    steps_r.
    iMod ("close" with "[↦offer ↦head Hoffer Hlist H↦ Hs]") as "_".
    { iLeft. iFrame. }

    (* comparison - which leads us to offering *)
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    iCombine "Hval" "Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval"); [prove_inline_cond|ss|eauto| | ].
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    destruct (decide (succ = 0)); subst; cycle 1.
    { exfalso; destruct stack_rep1, stack_rep; inv Hcomp; des_ifs. }

    (* make an offer *)
    steps_r. sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    iApply wsim_mem_alloc; [prove_inline_cond|ss|ss|].
    iIntros (offerb) "[↦offer [↦offerst _]]".
    steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    store_r "↦offer".
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    store_r "↦offerst".
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    clear dependent l l1 stack_rep stack_rep1 offer_rep offer_rep1.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }

    store_r "Hoffer↦".
    iMod (own_alloc (Excl ())) as "[%γo OfferTkn]"; ss.
    iMod (inv_alloc
      (syn_offer_inv n γo (offerb, 0%Z) req_id (stid, mtid, (n, Vptr (stackb, stackofs), v, γs)))
      _ _ _ (offerN N) with "[↦offer ↦offerst Help]") as "#Hoinv"; eauto.
    { solve_ndisj. }
    { solve_base_sl_red; iFrame; auto. }

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { iLeft. iFrame. solve_base_sl_red. iExists γo, _, _. iSplit; eauto. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    clear dependent l stack_rep offer_rep.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist [Hoffer↦ _]]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      by iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid.
    }
    store_r "Hoffer↦".

    iMod ("close" with "[Hoffer↦ Hlist H↦ Hs]") as "_".
    { iLeft; iFrame. solve_base_sl_red. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    iInv "Hoinv" as "[%offerst [offerst↦ offer]] /=" "close".
    rewrite Z.add_0_l.
    case_decide; subst.
    { (* nobody helped*)
      iApply (wsim_mem_cas with "offerst↦"); [prove_inline_cond|ss|eauto| | | ].
      { instantiate (1:=emp%I); done. }
      { eauto. }
      case_bool_decide; ss. iIntros "Hofferst _". steps_r.

      iMod ("close" with "[Hofferst OfferTkn]") as "_".
      { iFrame. done. }

      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r.

      by_coind CIH. iDestruct "offer" as "[? ?]"; iFrame. done.
    }
    case_decide; subst.
    { (* Somebody helped *)
      iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "offerst↦");
        [prove_inline_cond|try prove_sb_cond|ss|..]; eauto.
      case_bool_decide; ss. iIntros "Hofferst _". steps_r.
      iPoseProof "offer" as "#offer".

      iMod ("close" with "[Hofferst]") as "_".
      { iFrame. done. }

      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      iAssert (emp)%I as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r.

      sch_yield_l. steps_l.
      iApply (wsim_helping_done_try_run with "offer IST"); eauto.
      iIntros "IST".
      sch_yield_l. steps_l. sch_yield_l. force_l. iFrame. iSplit; eauto.
      step. iFrame. eauto.
    }

    case_decide; try by (iCombine "OfferTkn" "offer" gives %WF). ss.
  Unshelve. all: try exact 1%Qp.
  (*SLOW*)Qed.

End StackIM.