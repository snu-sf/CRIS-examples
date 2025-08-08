Require Import CRIS.
Require Import ImpPrelude.
Require Import SchHeader SchA SchTactics.
Require Import MemHeader MemA.
From CRIS.increment Require Import Header.

Module IncrementA. Section IncrementA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG}.

  Definition scopes : list string := [].

  Definition increment : list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
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

  Definition fnsems : fnsems_type :=
    [(Some IncrementHdr.increment, (true, wmask_all, scopes, (None, (cfunU increment))))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End IncrementA. End IncrementA.
