Require Import CRIS.
Require Import ImpPrelude.
Require Import SchHeader SchA SchTactics.
Require Import MemHeader MemA.
From CRIS.increment Require Import Header.

Module IncrementA. Section IncrementA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
                     
  Definition increment_spec : fspec :=
    fspec_sch ∅
      (fspec_simple (λ bofs,
        ((λ varg, ⌜varg = [Vptr bofs]↑⌝),
        (λ vret, True))
      ))%I.

  Definition sp : alist string fspec :=
    [(IncrementHdr.increment, increment_spec)].

  Definition scopes : list string := [].

  Definition increment2 : list val → itree hmodE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)!;;
      𝒴;;;
      iterC (λ _ : unit,
        𝒴;;;
        v <- trigger (Take Z);;
        trigger (Assume (bofs ↦ Vint v));;;
        'b : bool <- trigger (Choose bool);;
        if b
        then trigger (Guarantee (bofs ↦ Vint (v + 1)));;; 𝒴;;; Ret (inr (Vint v))
        else trigger (Guarantee (bofs ↦ Vint v));;; 𝒴;;; Ret (inl tt)
      ) ().

  Definition increment : list val → itree hmodE val :=
    λ arg, increment2 arg.

  Definition fnsems :=
    [(IncrementHdr.increment, (wmask_all, scopes, mk_specbody (increment_spec) (cfunN increment)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (SMod.to_hmod (to_sp (SchAS.sp ∅ sp_empty)) Mod).
End IncrementA. End IncrementA.
