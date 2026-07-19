Require Import CRIS.common.CRIS.
Require Import CRIS.scheduler.SchHeader.
Require Import RRSHeader.
Require Import NDSHeader.
Require Import RRSNodeHeader.
Require Import NDSNodeHeader.
Set Implicit Arguments.

Module SCHMainI. Section SCHMainI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      (** Initializing nodes **)
      ccallU SchHdr.spawn (RRSHdr.init.1, RRSNodeHdr.f_main.1↑↑);;;
      ccallU SchHdr.spawn (NDSHdr.init.1, NDSNodeHdr.f_main.1↑↑);;;
      (** Starting nodes **)
      𝒴;;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[entry # (msk_real (msk_scp [] msk_true), (None, main))]}.
  
  Program Definition smod: SMod.t :=
    {|
      SMod.scopes := [];
      SMod.fnsems := fnsems;
      SMod.initial_st := ∅;
    |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End SCHMainI. End SCHMainI.
