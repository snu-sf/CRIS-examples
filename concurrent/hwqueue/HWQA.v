Require Export CRIS.common.CRIS.
From CRIS.scheduler Require Export Atomic SchHeader.
From CRIS.imp_system Require Export imp.ImpPrelude.
From CRIS.hwqueue Require Export HWQHeader.
From CRIS.imp_system Require Export mem.MemHeader.
Require Export CRIS.prophecy.ProphecyHeader CRIS.helping.HelpingHeader.
Require Export CRIS.simulations.filter.CallFilter.
From CRIS.imp_system Require Export mem.MemA.
Require Export CRIS.scheduler.SchA CRIS.prophecy.ProphecyA.
From CRIS.hwqueue Require Export HWQRA.
From CRIS.imp_system Require Import mem.MemI mem.MemIAproof mem.MemTactics.
From CRIS.prophecy Require Import ProphecyI ProphecyFacts.
Require Import CRIS.helping.HelpingTactics.
From CRIS.hwqueue Require Import HWQI HWQP.
From CRIS.scheduler Require Import SchI SchTactics.
From stdpp Require Import streams list.

(* Specification of the queue operations *)
Module HWQA. Section HWQA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.

  Definition scopes : list string := [].

  Definition new_queue : fbody := λ arg,
    {{{ ∀∀ '((n, sz) : nat * nat), ⌜arg = [Vint sz]↑ ∧ 0 < 8 * (2 + sz) < modulus_64⌝%Z }}}
      𝒴@{Some N};;; trigger (Choose (Any.t * ()))
    {{{ RET ret, ∃ q γq, ⌜ret = q↑⌝ ∗ is_hwq n N sz γq q ∗ hwq_cont γq [] }}} @ N.

  Definition enqueue : fbody := λ arg,
    {{{ ∀∀ '((γq, l) : gname * val),
        ∃ blk ofs q n sz, ⌜arg = [q; l]↑ ∧ l = Vptr (blk, ofs)⌝ ∗ is_hwq n N sz γq q ∗ ∃ v, (blk, ofs) ↦ v }}}
      <<{ ∀∀ (ls : list valO), hwq_cont γq ls, hwq_cont γq (ls ++ [l]) }>> @ N
    {{{ emp }}} @ N.

  Definition dequeue : fbody := λ arg,
    {{{ ∀∀ (γq : gname),
        ∃ q n sz, ⌜arg = [q]↑⌝ ∗ is_hwq n N sz γq q }}}
      <<{ ∀∀ (ls : list valO), hwq_cont γq ls, ∃∃ ret, ∃ l ls', ⌜ret = l↑ ∧ ls = l :: ls'⌝ ∗ hwq_cont γq ls' }>> @ N
    {{{ emp }}} @ N.

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_scp scopes msk_true, (None, new_queue));
      fid HWQHdr.enqueue   # (msk_scp scopes msk_true, (None, enqueue));
      fid HWQHdr.dequeue   # (msk_scp scopes msk_true, (None, dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End HWQA. End HWQA.

Module HWQM. Section HWQM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mn : string).

  (* the job to help: enqueue *)
  Definition jobCode : SAny.t → itree crisE (SAny.t + SAny.t) := λ arg,
    '(v, γq) : val * gname <- (arg↓↓)?;;
    ls <- trigger (Take (list valO));;
    trigger (Assume (hwq_cont γq ls));;;
    trigger (Guarantee (hwq_cont γq (ls ++ [v])));;;
    Ret (inr Vundef↑↑).

  Definition scopes : list string := [].

  Definition enqueue : fbody := λ arg,
    {{{ ∀∀ '((γq, l) : gname * val), ∃ blk ofs q n sz,
        ⌜arg = [q; l]↑ ∧ l = Vptr (blk, ofs)⌝ ∗ is_hwq n N sz γq q ∗ ∃ v, (blk, ofs) ↦ v }}}
      trigger (Call (Helping.run mn) (Some N, (l, γq)↑↑)↑);;;
      ITree.iter (λ _,
        'b : bool <- trigger (Choose bool);;
        if b 
        then trigger (Call (Helping.help mn) ((Some N)↑));;; Ret (inl ()) 
        else Ret (inr ())) ();;;
      𝒴@{Some N};;; Ret (Vundef↑, tt)
    {{{ emp }}} @ N.

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_scp scopes msk_true, (None, HWQA.new_queue));
      fid HWQHdr.enqueue   # (msk_scp scopes msk_true, (None, enqueue));
      fid HWQHdr.dequeue   # (msk_scp scopes msk_true, (None, HWQA.dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End HWQM. End HWQM.
