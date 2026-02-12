Require Import CRIS.
Require Import SchHeader.
Require Import RRSHeader.
Require Import NDSHeader.
Require Import RRSNodeHeader.
Require Import NDSNodeHeader.
Set Implicit Arguments.

Module SCHMainI. Section SCHMainI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concGS}.

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      (** Initializing nodes **)
      trigger (Call SchHdr.spawn (RRSHdr.init, RRSNodeHdr.f_main↑↑)↑);;;
      trigger (Call SchHdr.spawn (NDSHdr.init, NDSNodeHdr.f_main↑↑)↑);;;
      (** Starting nodes **)
      𝒴;;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[None := Some (msk_real (msk_scp [] msk_true), (None, main))]}.
  
  Program Definition smod: SMod.t :=
    {|
      SMod.scopes := [];
      SMod.fnsems := fnsems;
      SMod.initial_st := ∅;
    |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End SCHMainI. End SCHMainI.

