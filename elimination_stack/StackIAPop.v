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
  Local Notation StackM := (SchI ★ MemA ★ StackM.t mn N ((SchA.sp ∅ (↑N))) ★ HelpingOn).
  Local Notation StackI := (SchI ★ MemA ★ CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy).

  Local Notation IstFull := (HelpingTactics.IstFull StackM.jobID StackM.retID mn).

  Lemma pop_simF : ISim.sim_fun open StackM StackI IstFull (fid StackHdr.pop).
  Proof using.
    iStartSim.
    rewrite /StackM.pop /atomic_body.
    steps_l. destruct _q as [[stid mtid] [[n vs] γs]].
    iDestruct "ASM" as "[TID [_ [-> #[%stackb [%stackofs [-> Hinv]]]]]]". steps_r.

    (* Coinduction starts here *)
    iApply wsim_reset. iStopProof.
    revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_tgt st_src]) "[#Hinv [IST TID]] /=".
    destruct_quant CIH.

    unfold_iter_r. rewrite {1}/StackI._pop. steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* Stack load *)
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }

    load_r "H↦".

    destruct (decide (stack_rep = Vint 0%Z)); subst.
    { (* Empty stack - terminate *)
      sch_yield_l. steps_l. force_l false. steps_l.

      (* Atomic update *)
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      destruct l; [|ss; iPoseProof "Hlist" as "[% [% [% [% [% [% ?]]]]]]"; clarify].
      force_l. iFrame. steps_l.

      iMod ("close" with "[Hs Hlist Hoffer H↦]") as "_".
      { iLeft. iFrame. }
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      sch_yield_l. force_l. iFrame. iSplit; eauto. step. iSplit; done.
    }
    (* Stack nonempty *)
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval #Hcomp]]".

    destruct l as [|v l]; ss; first iPoseProof "Hlist" as "%"; clarify.
    iDestruct "Hlist" as (headb headofs stackrep q0 q1) "[-> [↦v [↦next Hlist]]]".
    iDestruct "↦next" as "[↦next ↦next2]".
    iMod ("close" with "[Hs Hlist H↦ ↦v ↦next2 Hoffer]") as "_".
    { iLeft. iFrame. iExists _, _, _, _; iFrame; eauto. }

    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    load_r "↦next".
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    iInv "Hinv" as "[[%stack_rep' [%offer_rep' [%l' [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iPoseProof (list_inv_comparable with "Hlist") as "[Hlist [Hval2 _]]".
    iPoseProof ("Hcomp" with "Hlist") as "[%succ %Hcomp]".

    iCombine "Hval Hval2" as "Hcmp".
    iApply (wsim_mem_cas with "H↦ Hcmp");
      [prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "H↦ [Hval Hval2]". iClear "Hcomp". steps_r.
    case_bool_decide; subst.
    { (* Pop success *)
      sch_yield_l. steps_l. force_l false. steps_l.
      destruct (stack_rep') as [[| |]|[bold ofsold]|]; inv Hcomp; case_bool_decide; ss.
      destruct l'; ss.
      { iPoseProof "Hlist" as "%"; ss. }
      iDestruct "Hlist" as "[% [% [% [% [% [% [Hpt1 [Hpt2 Hlist]]]]]]]]". des; clarify.
      iPoseProof (mem_points_to_singleton_agree with "↦next Hpt2") as "<-".
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs ASM]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l; iFrame. steps_l.
      iMod ("close" with "[Hs Hlist H↦ Hoffer]") as "_".
      { iLeft. iFrame. }
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

      iCombine "Hval Hval2" as "Hval".
      iApply (wsim_mem_cmp with "Hval");
        [try prove_inline_cond|try prove_sb_cond|ss|..]; eauto.
      { case_bool_decide; ss; exfalso; naive_solver. }
      { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
      iIntros "[[% [% Hval]] _]". steps_r.
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

      load_r "Hval".
      iPoseProof (mem_points_to_singleton_agree with "Hval Hpt1") as "<-".
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      sch_yield_l. force_l. iFrame. iSplit; eauto. step. iFrame. eauto.
    }

    (* Pop failure *)
    iMod ("close" with "[↦next Hs Hoffer Hlist H↦]") as "_".
    { iLeft. iFrame. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. } steps_r.
    iCombine "Hval Hval2" as "Hval".
    iApply (wsim_mem_cmp with "Hval");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { iIntros "[[% [% $]] [% [% $]]] !> [$ $] //". }
    iIntros "_". steps_r.
    assert (succ = 0%Z); last subst succ.
    { destruct stack_rep' as [[|?|?]|[? ?]|]; inv Hcomp; ss; case_bool_decide; des; clarify; ss. }
    steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* Check the offer *)
    clear dependent stack_rep' offer_rep offer_rep' l  l'.
    iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "close";
      cycle 1.
    { iExFalso. iDestruct "IST" as "[% [% [% [% [% [? [% [% [IST ●2]]]]]]]]]".
      iCombine "●" "●2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss.
    }
    iDestruct "Hoffer" as "[↦offer Hoffer]".
    load_r "↦offer".
    rewrite /syn_is_offer; destruct (offer_rep) as [[|?|?]|[offerb offerofs]|]; solve_base_sl_red;
      try iPoseProof ("Hoffer") as "%"; ss.
    { steps_r.
      iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
      { iLeft; iFrame. solve_base_sl_red. }
      by_coind CIH. iFrame. done.
    }
    iDestruct "Hoffer" as (γo [[stid' mtid'] [[[n' s'] v'] γs']] reqid) "[OfferInv <-]".
    iPoseProof ("OfferInv") as "#OfferInv".

    steps_r.
    iMod ("close" with "[Hs H↦ Hlist ↦offer]") as "_".
    { iLeft; iFrame. solve_base_sl_red. repeat iExists _; iSplit; eauto. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    (* Try to take the offer *)
    iInv "OfferInv" as "[%offerst [↦offerst offer]] /=" "close".

    case_decide; subst.
    { (* Helping *)
      iDestruct "offer" as "[offerv offer]".
      iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cas with "↦offerst E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "offer↦ _". iClear "E". case_decide; last done.
      steps_r.

      (* Help *)
      sch_yield_l. force_l true. steps_l.
      rewrite {3}/SchA.sp; simpl_map.
      inline_l. steps_l.
      iDestruct "IST" as "[% [% [% [% [[-> ->] [IST [% [% [[-> ->] ●Help]]]]]]]]]".
      iPoseProof (helping_auth_token with "●Help offer") as "%Hreq".
      iMod (helping_auth_commit with "●Help offer") as "[●offer #◯offer]".
      iMod ("close" with "[offer↦ ◯offer]") as "_".
      { iExists 1; iFrame; case_decide; ss. }
      rewrite /HelpingOn.help. force_l reqid. steps_l.
      assert (Hsp : (SchA.sp ∅ (↑N)).1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec (↑N))).
      { rewrite /SchA.sp; simpl_map; ss. }
      rewrite !Hsp.
      force_l (stid, mtid, tt). forces_l. iFrame. iSplit; eauto. steps_l.
      destruct _q as [[stid1 mtid1] []]. iDestruct "ASM" as "[TID [_ ->]]".

      (* Helpee's Atomic Assume *)
      rewrite /HelpingOn.try_run. steps_l. rewrite Hreq /=.
      steps_l.
      clear dependent stack_rep offer_rep l.
      iInv "Hinv" as "[[%stack_rep [%offer_rep [%l [Hs [H↦ [Hlist Hoffer]]]]]]|[% ●]]" "Close";
        cycle 1.
      { iExFalso. iCombine "●" "●offer" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss. }
      iCombine "Hs ASM" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hs ASM") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }

      (* Helpee's Atomic Guarantee *)
      force_l; iFrame "Hl". steps_l.

      (* My Atomic Assume *)
      iPoseProof (helping_auth_split (1/2) with "●offer") as "[●offer ●reclaim]"; ss.
      iMod ("Close" with "[●offer]") as "_".
      { iRight; iFrame. }
      forces_l. iFrame; iSplit; eauto. steps_l.
      iDestruct "ASM" as "[TID [_ ->]]".
      iCombine "Hs ASM'" gives %[->%Excl_included%leibniz_equiv _]%auth_both_valid_discrete. ss.
      iMod (own_update_2 with "Hs ASM'") as "[Hs Hl]".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      force_l; iFrame "Hl"; steps_l.
      iInv "Hinv" as "[[% [% [% [Hs' _]]]]|[% ●]]" "close".
      { iExFalso. iCombine "Hs" "Hs'" gives %WF; inv WF. }
      iPoseProof ("●reclaim" with "●") as "●".
      iMod ("close" with "[- IST TID ● offerv]") as "_".
      { iLeft; iFrame. }
      iIst "IST" with "[● IST]".
      { iExists _, _, _, _; iFrame. iSplit; eauto. iPureIntro; esplits; eauto; set_solver. }
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

      iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cmp with "E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
      iIntros "_". steps_r.
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

      (* Compare *)
      load_r "offerv".
      sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }
      sch_yield_l. forces_l. iFrame. iSplit; eauto. step. iFrame. done.
    }

    (* Failed to take the offer - repeat the whole process! *)
    iAssert (emp)%I with "[]" as "E"; first done.
      iApply (wsim_mem_cas with "↦offerst E");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). case_bool_decide; ss; des_ifs; ss. }
    iIntros "↦offerst _". steps_r.
    iMod ("close" with "[↦offerst offer]") as "_".
    { iExists _; ss; iFrame. case_decide; clarify. case_decide; eauto. case_decide; clarify. }
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    iApply (wsim_mem_cmp with "E");
      [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { instantiate (1:=0%Z). case_bool_decide; clarify; des_ifs; ss. }
    iIntros "_". steps_r.
    sch_yield_ir "IST" "TID". { case_bool_decide; set_solver. }

    by_coind CIH. iFrame. done.
  (*SLOW*)Qed.
End StackIM.
