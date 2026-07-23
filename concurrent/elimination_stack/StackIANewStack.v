Require Import CRIS.common.CRIS.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.imp_system Require Import mem.MemTactics mem.MemA.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.elimination_stack Require Import StackHeader StackA StackI.
From CRIS.filter Require Import CallFilter.
From CRIS.helping Require Import HelpingTactics.

Section StackIM.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !stackGS}.

  (* Helping module being parameterized by mn *)
  Context (mn : string).
  Context (sp : specmap).

  Local Notation MemA := (CFilter.filter (Helping.exports mn) (MemA.t sp)).
  Local Notation SchI := (CFilter.filter (Helping.exports mn) SchI.t).
  Local Notation HelpingOn := (HelpingOn.t mn (StackM.jobCode)).
  Local Notation HelpingDummy := (HelpingDummy.t mn).
  Local Notation StackM := ((StackM.t mn ★ HelpingOn) ★ MemA ★ SchI).
  Local Notation StackI := ((CFilter.filter (Helping.exports mn) StackI.t ★ HelpingDummy) ★ MemA ★ SchI).

  Lemma new_stack_simF ist : ISim.sim_fun open StackM StackI ist (fid StackHdr.new_stack).
  Proof using.
    cStartFunSim. rewrite /= /StackI.new_stack /StackM.new_stack. cStepS.
    aStepS (N n) "[%v ->]". cStepsT. sYields.
    mAllocT as (blk) "[↦stack [↦val _]]". sYields.

    (* initialize stack *)
    mStore. sYields. mStore. sYields.

    (* Guarantee the postcondition *)
    sYieldS.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_both_valid_discrete. split; done. }
    iMod (hinv_alloc (syn_stack_inv N n γs blk 0%Z) _ _ (stackN N) with "[-Hs◯ IST]")
      as "#[%γ Hinv]"; eauto.
    { solve_ndisj. }
    { rewrite sl_red; iFrame; eauto. }

    cForceS ((Vptr (blk, 0%Z))↑, tt). cStep; iFrame. iModIntro. iSplit; iFrame "#"; eauto.
  (*SLOW*)Qed.
End StackIM.
