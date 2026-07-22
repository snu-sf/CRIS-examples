Require Import CRIS.common.CRIS.
Require Import CRIS.filter.CallFilter.
From CRIS.scheduler Require Import SchHeader SchA.
From CRIS.scheduler Require Import RRS.RRSHeader RRS.RRSA.
From CRIS.scheduler Require Import NDS.NDSHeader NDS.NDSA.
From CRIS.scheduler Require Import example.RRSNodeHeader example.RRSNodeA.
From CRIS.scheduler Require Import example.NDSNodeHeader example.NDSNodeA.
From CRIS.imp_system Require Import mem.MemHeader mem.MemA.
From CRIS.scheduler Require Import example.SCHMainI.
Set Implicit Arguments.

Module SCHMainA. Section SCHMainA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !SchA.schGS}.
  Context `{_rrsG: !RRSA.rrsGS}.
  Context `{_ndsG: !NDSA.ndsGS}.
  Context `{_memGS: !MemA.memGS}.
  Context `{_nodeG: !RRSNodeA.nodeGS}.
  Import SCHMainI.

  Definition main_spec E : fspec :=
    fspec_winv E
      (fspec_simple (λ (_: unit),
           ((λ arg, RRSAS.InitRRS ∗ RRSNodeAS.full_val (Vint 0) ∗ NDSA.InitNDS ∗ SchA.Tid 0 0)%I,
            (λ ret, True)%I))).

  Definition sp E : specmap :=
    {[entry @ (main_spec E)]}.

  Definition fnsems (E : coPset) : fnsemmap :=
    {[entry # (msk_scp [] msk_true, (fsp_some (main_spec E), main))]}.

  Program Definition smod E: SMod.t :=
    {|
      SMod.scopes := [];
      SMod.fnsems := fnsems E;
      SMod.initial_st := ∅;
    |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := RRSAS.InitRRS ∗ RRSNodeAS.full_val (Vint 0) ∗ NDSA.InitNDS ∗ SchA.TidFrag 0 0.

  Definition t sp := SMod.to_mod sp (smod ⊤).
End SCHMainA. End SCHMainA.
