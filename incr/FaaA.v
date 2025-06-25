Require Import CRIS.
Require Import ImpPrelude MemHeader MemA SchA SchTactics SchHeader.
From CRIS.incr Require Import Header.

Module FaaA. Section FaaA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.

  Definition faa2_spec : fspec :=
    fspec_sch ∅ (fspec_simple (λ bofs, (λ arg, ⌜arg = [Vptr bofs]↑⌝, λ ret, ⌜ret = tt↑⌝)))%I.

  Definition sp : alist string fspec :=
    [(FaaHdr.faa2, faa2_spec)].

  Definition scopes : list string := [].

  Definition faa2 : list val → itree hmodE unit :=
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

  Definition fnsems := [(FaaHdr.faa2, (wmask_all, scopes, mk_specbody faa2_spec (cfunN faa2)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (SMod.to_hmod (to_sp (SchAS.sp ∅ sp_empty)) Mod).
End FaaA. End FaaA.