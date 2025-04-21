Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader MemA SchA SchTactics SchHeader.

Module FaaA. Section FaaA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.

  Definition faa2_spec u : fspec :=
    sch_fspec u (fspec_simple (λ bofs, (λ arg, ⌜arg = [Vptr bofs]↑⌝, λ ret, ⌜ret = tt↑⌝)))%I.

  Definition sp u : alist string fspec :=
    [(FaaHdr.faa2, faa2_spec u)].

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

  Definition fnsems u := [(FaaHdr.faa2, (scopes, mk_specbody (faa2_spec u) (cfunN faa2)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems u;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t u sp : HMod.t := Seal.sealing CRIS (SMod.to_hmod sp (Mod u)).
End FaaA. End FaaA.
