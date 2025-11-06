Require Import CRIS.
Require Import IncrHeader ImpPrelude.
Require Import MemHeader MemA.
Require Import SchHeader SchTactics SchA.

Module IncrA. Section IncrA.
  Context `{_crisF: !crisG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.

  Definition scopes : list string := [].

  Definition incr : list val → itree crisE val :=
    λ arg,
      '(b, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)?;;
      𝒴;;;
        v <- trigger (Take Z);;
        trigger (Assume ((b, ofs) ↦ Vint v));;;
        trigger (Guarantee ((b, ofs) ↦ Vint (v + 1)));;;
      𝒴;;; Ret Vundef.

  Definition incr_spec q : fspec :=
    fspec_sch q
      (fspec_simple (λ bofs,
        (λ arg, ⌜arg = [Vptr bofs]↑⌝,
        λ ret, ⌜ret = Vundef↑⌝)))%I.

  Definition fnsems q : fnsems_type := [(Some IncrHdr.incr, (true, wmask_all, scopes, (Some (incr_spec q), cfunU incr)))].

  Program Definition Mod q : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems q;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Program Definition t q sp : Mod.t :=
    Seal.sealing CRIS (SMod.to_mod sp (Mod q)).
End IncrA. End IncrA.
