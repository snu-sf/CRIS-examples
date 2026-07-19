Require Import CRIS.common.CRIS CRIS.scheduler.Atomic.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.scheduler Require Import SchHeader SchA.
From CRIS.imp_system Require Import mem.MemHeader mem.MemA.
From CRIS.incr Require Import IncrHeader.

Module IncrA. Section IncrA.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS, !schGS}.

  Definition scopes : list string := [].

  Definition incr : fbody := λ arg,
    {{{ ∀∀ bofs, ⌜arg = [Vptr bofs]↑⌝ }}}
      <<{ ∀∀ v, bofs ↦ Vint v, bofs ↦ Vint (v + 1) }>> @ N
    {{{ ∀∀ v, RET ret, ⌜ret = (Vint v)↑⌝ }}} @ N.

  Definition fnsems : fnsemmap :=
    {[fid IncrHdr.incr # (msk_scp scopes msk_true, (None, incr))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End IncrA. End IncrA.
