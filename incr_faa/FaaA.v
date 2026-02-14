Require Import CRIS.
Require Export ImpPrelude MemHeader MemA SchHeader.
Require Export FaaHeader.

Module FaaA. Section FaaA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition scopes : list string := [].

  Definition faa2 : list val → itree crisE unit :=
    λ arg,
      '(b, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)?;;
      𝒴;;;
        'v : Z <- trigger (Take Z);;
        trigger (Assume ((b, ofs) ↦ Vint v));;;
        trigger (Guarantee ((b, ofs) ↦ Vint (v + 1)));;;
      𝒴;;;
        'v : Z <- trigger (Take Z);;
        trigger (Assume ((b, ofs) ↦ Vint v));;;
        trigger (Guarantee ((b, ofs) ↦ Vint (v + 1)));;;
      𝒴;;; Ret tt.

  Definition fnsems : fnsemmap :=
    {[Some FaaHdr.faa2 := Some (msk_scp scopes msk_true, (None, cfunU faa2))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End FaaA. End FaaA.