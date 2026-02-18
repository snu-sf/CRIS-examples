Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI StackIAPush StackIAPop StackIANewStack.
Require Export HelpingTactics HelpingFacts.

Module StackIM. Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS, !stackG StackM.jobID StackM.retID}.
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

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI init_cond IstFull.
  Proof.
    rewrite assoc (assoc _ SchI).
    eapply ISim_reflL.
    { rewrite -!assoc.
      intros fn; rewrite Mod.dom_fnsems_add; set_unfold; i; des; subst.
      { apply new_stack_simF. }
      { apply push_simF. }
      { apply pop_simF. }
      { iStartSim; steps_r. steps_r; ss. }
      { iStartSim; steps_r. steps_r; ss. }
    }
    { multiset_solver. }
    { multiset_solver. }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { mod_tac. }
    { iIntros "I"; repeat iExists _; iFrame; iPureIntro; splits; eauto; ss.
      { rewrite dom_union_with; set_solver. }
      { rewrite left_id_L //. }
    }
  Qed.
End StackIM. End StackIM.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS, !stackG StackM.jobID StackM.retID}.

  Lemma ctxr (N : namespace) (sp sp_user : specmap) :
    SchA.sp sp_user (↑N) ⊆ sp →
    ctx_refines
      (StackA.t N sp ★ MemA.t sp ★ SchI.t, StackIM.init_cond)
      (StackI.t      ★ MemA.t sp ★ SchI.t, emp%I).
  Proof.
    intros Hsp.
    etrans; first eapply ctxr_cond_strengthen.
    { instantiate (1:=(_ ∗ emp)%I); iIntros "H"; iSplitL; last done; iExact "H". }
    eapply helping_main with (mM:=λ mn, StackM.t mn N ((SchA.sp ∅ (↑N)))).
    { intros mn.
      rewrite ?CFilter.filter_app -?assoc.
      ctxr_swap. ctxr_rotate. ctxr_swap. do 3 ctxr_rotate. ctxr_swap.
      etrans; cycle 1.
      { eapply main_adequacy, StackIM.sim with (mn:=mn) (N:=N). }
      etrans; cycle 1.
      { do 2 ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_swap. do 2 ctxr_drop. refl. }
      rewrite left_id. refl.
    }
    intros mn.
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_swap. ctxr_refl. }

    rewrite assoc.
    eapply main_adequacy with (Ist := IstProd (IstSB (Mod.scopes (StackA.t N sp) ++ [mn]) IstTrue) IstEq).
    init_sim.
    { iStartSim.
      steps_l. force_r _q. destruct _q as [[? ?] ?]; iDestruct "ASM" as "[? [-> [% ->]]]".
      forces_r. iFrame; iSplit; eauto.
      steps_l; steps_r.
      sch_yield_ii "IST". sch_yield_l.
      steps_r; forces_l. iFrame; step. iFrame. done.
    }
    { iStartSim.
      rewrite /StackA.push /StackM.push /atomic_body.
      steps_l. steps_r. forces_r. iFrame "ASM". repeat case_match; clarify.
      steps_r.
      sch_yield_ii "IST".
      rewrite /SchA.sp; simpl_map.
      inline_r. rewrite /HelpingOff.HelpingOff.run. steps_r.
      sch_yield_ii "IST". sch_yield_l.
      steps_l. forces_r; iFrame. steps_r. forces_l. iFrame.
      steps_l. sch_yield_ii "IST". steps_r. 
      sch_yield_ii "IST". steps_r. 
      sch_yield_l; force_l; iFrame.
      step. iFrame. done.
    }
    { iStartSim.
      rewrite /StackA.pop /StackM.pop /atomic_body.
      steps_l. steps_r. forces_r. iFrame "ASM". repeat case_match; clarify.
      steps_r. steps_l.
      sch_yield_ii "IST".
      set (IstFull := IstProd _ _).
      steps_r. iApply wsim_bind; iSplitL.
      { instantiate (1:=λ x y, IstFull x.1 y.1).
        add_ret_l. case_match.
        { steps_r. rewrite /SchA.sp; simpl_map. inline_r.
          rewrite /HelpingOff.HelpingOff.help. steps_r.
          sch_yield_ii "IST". steps_r. sch_yield_l. step. iFrame.
        }
        { steps_r. sch_yield_l. step. iFrame. }
      }
      clear_st. iIntros (st_src [] st_tgt ?) "IST /=".
      steps_l. forces_r; iFrame. steps_r. forces_l. iFrame.
      steps_l. sch_yield_ii "IST".
      sch_yield_l; force_l; iFrame.
      step. iFrame. done.
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.
End StackIA. End StackIA.
