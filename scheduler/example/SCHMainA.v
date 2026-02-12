Require Import CRIS.
Require Import CallFilter.
Require Import SchHeader SchA.
Require Import RRSHeader RRSA.
Require Import NDSHeader NDSA.
Require Import RRSNodeHeader RRSNodeA.
Require Import NDSNodeHeader NDSNodeA.
Require Import MemHeader MemA.
Require Import SCHMainI.
Set Implicit Arguments.

Module SCHMainA. Section SCHMainA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concGS}.
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
    {[speckey_entry := fspec_to_rel (main_spec E)]}.

  Definition fnsems (E : coPset) : fnsemmap :=
    {[None := Some (msk_scp [] msk_true, (fsp_some (main_spec E), main))]}.

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
