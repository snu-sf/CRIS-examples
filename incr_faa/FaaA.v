Require Import CRIS.
Require Import ImpPrelude MemHeader MemA SchA SchTactics SchHeader.
From CRIS.incr_faa Require Import Header.

Module FaaA. Section FaaA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG}.

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

  Definition fnsems : fnsems_type :=
    [(Some FaaHdr.faa2, (true, wmask_all, scopes, (None, cfunU faa2)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End FaaA. End FaaA.
