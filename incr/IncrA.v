Require Import CRIS Atomic.
Require Import ImpPrelude.
Require Import SchHeader SchA.
Require Import MemHeader MemA.
Require Import IncrHeader.

Module IncrA. Section IncrA.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS, !schGS}.

  Definition scopes : list string := [].

  Definition incr (N : namespace) : fbody := λ arg,
    {{{ ∀∀ bofs, ⌜arg = [Vptr bofs]↑⌝ }}}
      <<{ ∀∀ v, bofs ↦ Vint v, bofs ↦ Vint (v + 1) }>>
    {{{ ∀∀ v, RET ret, ⌜ret = (Vint v)↑⌝ }}} @ N.

  Definition fnsems (N : namespace) : fnsemmap :=
    {[fid IncrHdr.incr # (msk_scp scopes msk_true, (None, incr N))]}.

  Program Definition smod N : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems N;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t N : Mod.t := SMod.to_mod (SchA.sp ∅ (↑N)) (smod N).
End IncrA. End IncrA.
