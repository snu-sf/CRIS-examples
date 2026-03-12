Require Import CRIS Atomic.
Require Import ImpPrelude.
Require Import SchHeader SchA.
Require Import MemHeader MemA.
Require Import IncrHeader.

Module IncrA. Section IncrA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !concGS}.

  Definition scopes : list string := [].

  Definition incr_spec : fspec_atomic := {|
    meta_priv := mblock * ptrofs;
    meta_pub := Z;
    pre_priv := λ bofs arg, ⌜arg = [Vptr bofs]↑⌝;
    pre_pub := λ bofs v _, bofs ↦ Vint v;
    post_pub := λ bofs v ret, bofs ↦ Vint (v + 1);
    post_priv := λ bofs v ret, ⌜ret = (Vint v)↑⌝;
  |}%I.

  Definition fnsems : fnsemmap :=
    {[fid IncrHdr.incr #
        (msk_scp scopes msk_true,
          (None, atomic_fun incr_spec (atomic_update incr_spec)))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End IncrA. End IncrA.
