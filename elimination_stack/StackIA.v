Require Import CRIS.
Require Import ImpPrelude.
Require Import MemTactics MemA.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA StackI StackIAPush StackIAPop StackIANewStack.
Require Export HelpingTactics HelpingFacts.

Module StackIM. Section StackIM.
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

  (* Construct ISim.t for summing up each simulation proofs *)
  Lemma sim : ISim.t open StackM StackI init_cond IstFull.
  Proof.
    cStartModSim.
    - apply new_stack_simF.
    - apply push_simF.
    - apply pop_simF.
    - cStartFunSim; cStepsT. cStepsT; ss.
    - cStartFunSim; cStepsT. cStepsT; ss.
    - iIntros "I"; repeat iExists _; iFrame; iPureIntro; splits; eauto; ss.
      + rewrite dom_union_with; set_solver.
      + rewrite left_id_L //.
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
    etrans; first eapply ctxr_consequence.
    { instantiate (1:=(_ ∗ emp)%I); iIntros "H"; iSplitL; last done; iExact "H". }
    eapply helping_main; i; rewrite !CFilter.filter_app.
    { rewrite (comm _ _ (HelpingOn.t _ _ _)) assoc.
      etrans; [eapply main_adequacy, StackIM.sim|].
      rewrite -!assoc. ctxr_drop.
      do 2 ctxr_rotate. refl.
    }
    instantiate (1:= N); s.

    etrans; cycle 1.
    { do 3 ctxr_rotate. ctxr_swap. ctxr_refl. }
    rewrite (assoc _ (StackM.t _ _ _)).

    eapply main_adequacy with (Ist := IstProd (IstSB (Mod.scopes (StackA.t N sp) ++ [mn]) IstTrue) IstEq).
    cStartModSim.
    { cStartFunSim. rewrite /StackM.new_stack /StackA.new_stack.
      cStepsS. cForceT _q. destruct _q as [[? ?] ?]; iDestruct "ASM" as "[? [-> [% ->]]]".
      cForcesT. iFrame; iSplit; eauto.
      cStepsS; cStepsT.
      sYieldII "IST". sYieldS.
      cStepsT; cForcesS. iFrame; cStep. iFrame. done.
    }
    { cStartFunSim. rewrite /StackM.push /StackA.push.
      rewrite /StackA.push /StackM.push /atomic_body.
      cStepsS. cStepsT. cForcesT. iFrame "ASM". repeat case_match; clarify.
      cStepsT.
      sYieldII "IST".
      rewrite /SchA.sp; simpl_map.
      cInlineT. rewrite /HelpingOff.HelpingOff.run. cStepsT.
      sYieldII "IST". sYieldS.
      cStepsS. cForcesT; iFrame. cStepsT. cForcesS. iFrame.
      cStepsS. sYieldII "IST". cStepsT. 
      sYieldII "IST". cStepsT. 
      sYieldS; cForceS; iFrame.
      cStep. iFrame. done.
    }
    { cStartFunSim.
      rewrite /StackA.pop /StackM.pop /atomic_body.
      cStepsS. cStepsT. cForcesT. iFrame "ASM". repeat case_match; clarify.
      cStepsT. cStepsS.
      sYieldII "IST".
      set (IstFull := IstProd _ _).
      cStepsT. iApply wsim_bind; iSplitL.
      { instantiate (1:=λ x y, IstFull x.1 y.1).
        appendRetS. case_match.
        { cStepsT. rewrite /SchA.sp; simpl_map. cInlineT.
          rewrite /HelpingOff.HelpingOff.help. cStepsT.
          sYieldII "IST". cStepsT. sYieldS. cStep. iFrame.
        }
        { cStepsT. sYieldS. cStep. iFrame. }
      }
      clear_st. iIntros (st_src [] st_tgt ?) "IST /=".
      cStepsS. cForcesT; iFrame. cStepsT. cForcesS. iFrame.
      cStepsS. sYieldII "IST".
      sYieldS; cForceS; iFrame.
      cStep. iFrame. done.
    }
    { iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Qed.
End StackIA. End StackIA.
