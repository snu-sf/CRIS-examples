Require Import CRIS.
Require Import ImpPrelude MemHeader SchHeader.
Require Import FaaHeader.

Module FaaI. Section FaaI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition faa2 : list val → itree crisE unit :=
    λ arg, 𝒴;;; MemHdr.faa arg;;; 𝒴;;; MemHdr.faa arg;;; 𝒴;;; Ret tt.

  Definition fnsems : fnsemmap :=
    {[Some FaaHdr.faa2 := Some (msk_scp scopes (msk_real msk_true), (None, cfunU faa2))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End FaaI. End FaaI.