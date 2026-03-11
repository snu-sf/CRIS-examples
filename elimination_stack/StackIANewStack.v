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

  Local Notation IstFull := (HelpingTactics.IstFull StackM.jobID StackM.retID mn).

  Lemma new_stack_simF : ISim.sim_fun open StackM StackI IstFull (fid StackHdr.new_stack).
  Proof using.
    cStartFunSim. rewrite /StackI.new_stack /StackM.new_stack.
    cStepsS. destruct _q as [[stid mtid] n]. iDestruct "ASM" as "[TID [-> [%val ->]]]".
    cStepsS. cStepsT.
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    (* allocate new stack - can't use memtactics here..., generalize the lemma *)
    iApply wsim_mem_alloc; [try by simpl_map|ss|ss|].
    iIntros (blk) "[↦stack [↦val _]]". cStepsT.
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    (* initialize stack *)
    mStoreT "↦stack".
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    mStoreT "↦val".
    sYieldIR "IST" "TID". { case_bool_decide; set_solver. }

    (* Guarantee the postcondition *)
    sYieldS.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_both_valid_discrete. split; done. }
    iMod (inv_alloc (syn_stack_inv N γs blk 0%Z n) _ _ _ (stackN N) with "[-Hs◯ IST TID]")
      as "#Hinv"; eauto.
    { solve_ndisj. }
    { solve_base_sl_red. iLeft. iExists (Vint 0), (Vint 0), []; iFrame; solve_base_sl_red; ss. }

    cForceS (Vptr (blk, 0%Z)). cStepsS. cForcesS.
    iFrame "Hs◯ TID"; iSplit; eauto.
    { iSplit; eauto. iExists _; iSplit; eauto. iExists _, _; iSplit; eauto. }
    cStepsS. cStep. iSplit; eauto.
  (*SLOW*)Qed.
End StackIM.
