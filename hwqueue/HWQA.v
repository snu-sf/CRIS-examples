Require Export CRIS Atomic ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics.
Require Import HWQI HWQP SchI SchTactics.
From stdpp Require Import streams list.

(* Specification of the queue operations *)
Module HWQA. Section HWQA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !memGS, !prophGS, !hwqG}.
  Context (N : namespace).

  Definition scopes : list string := [].

  Definition new_queue : fbody := λ arg,
    {{{ ∀∀ '((n, sz) : nat * nat), ⌜arg = [Vint sz]↑ ∧ 0 < 8 * (2 + sz) < modulus_64⌝%Z }}}
      𝒴;;; trigger (Choose (Any.t * ()))
    {{{ RET ret, ∃ q γq, ⌜ret = q↑⌝ ∗ is_hwq N n sz γq q ∗ hwq_cont γq [] }}} @ N.

  Definition enqueue : fbody := λ arg,
    {{{ ∀∀ '((γq, l) : gname * val),
        ∃ blk ofs q n sz, ⌜arg = [q; l]↑ ∧ l = Vptr (blk, ofs)⌝ ∗ is_hwq N n sz γq q ∗ ∃ v, (blk, ofs) ↦ v }}}
      <<{ ∀∀ (ls : list valO), hwq_cont γq ls, hwq_cont γq (ls ++ [l]) }>>
    {{{ emp }}} @ N.

  Definition dequeue : fbody := λ arg,
    {{{ ∀∀ (γq : gname),
        ∃ q n sz, ⌜arg = [q]↑⌝ ∗ is_hwq N n sz γq q }}}
      <<{ ∀∀ (ls : list valO), hwq_cont γq ls, ∃∃ ret, ∃ l ls', ⌜ret = l↑ ∧ ls = l :: ls'⌝ ∗ hwq_cont γq ls' }>>
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

  Definition t sp := SMod.to_mod sp Mod.
End HWQA. End HWQA.

Module HWQM. Section HWQM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !memGS, !prophGS, !schGS, !hwqG}.
  Context (N : namespace) (mn : string).

  Notation jobID := (val * gname)%type. (* idx * gname *)
  Notation retID := val.

  Definition jobCode : jobID → itree crisE retID :=
    λ '(v, γq),
      ls <- trigger (Take (list valO));;
      trigger (Assume (hwq_cont γq ls));;;
      trigger (Guarantee (hwq_cont γq (ls ++ [v])));;;
      Ret Vundef.

  Definition scopes : list string := [].

  Definition enqueue : fbody := λ arg,
    {{{ ∀∀ '((γq, l) : gname * val), ∃ blk ofs q n sz,
        ⌜arg = [q; l]↑ ∧ l = Vptr (blk, ofs)⌝ ∗ is_hwq N n sz γq q ∗ ∃ v, (blk, ofs) ↦ v }}}
      ret <- trigger (Call (Helping.run mn) (l, γq)↑);;
      ITree.iter (λ _,
          'b : bool <- trigger (Choose bool);;
          if b 
          then trigger (Call (Helping.help mn) (()↑));;; Ret (inl ()) 
          else Ret (inr ())) ();;;
      𝒴;;; Ret (ret, tt)
    {{{ emp }}} @ N.

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_scp scopes msk_true, (None, HWQA.new_queue N));
      fid HWQHdr.enqueue   # (msk_scp scopes msk_true, (None, enqueue));
      fid HWQHdr.dequeue   # (msk_scp scopes msk_true, (None, HWQA.dequeue N))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod (SchA.sp ∅ (↑N)) Mod.
End HWQM. End HWQM.
