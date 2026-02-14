Require Import CRIS.
Require Import ImpPrelude.
Require Import SchHeader SchA.
Require Import MemHeader MemA.
Require Import IncrementHeader.

Module IncrementA. Section IncrementA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _CONC: !concGS}.

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

  Definition fnsems : fnsemmap :=
    {[Some IncrementHdr.increment := Some (msk_scp scopes msk_true, (None, cfunU increment))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End IncrementA. End IncrementA.
