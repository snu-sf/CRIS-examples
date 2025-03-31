Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader MemA SchA SchTactics SchHeader.

Module FaaA. Section FaaA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ}.

  Definition faa2_spec u : fspec :=
    w_fspec_sch u (fspec_simple (λ '(b, ofs), (λ arg, ⌜arg = [Vptr b ofs]↑⌝, λ ret, ⌜ret = tt↑⌝)))%I.

  Definition spc u : alist string fspec :=
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

  Definition t u spc : HMod.t := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) spc (Mod u)).
End FaaA. End FaaA.
