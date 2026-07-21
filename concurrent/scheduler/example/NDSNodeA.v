Require Import CRIS.common.CRIS.
From CRIS.scheduler Require Import SchHeader SchA.
From CRIS.scheduler Require Import NDS.NDSHeader NDS.NDSA.
From CRIS.hybrid_mem Require Import MemHdr MemLib HybridMem.
From CRIS.scheduler Require Import example.NDSNodeHeader example.NDSNodeI.
Require Import CRIS.simulations.filter.CallFilter.

Set Implicit Arguments.

Module NDSNodeA. Section NDSNodeA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !SchA.schGS}.
  Context `{_ndsG: !NDSA.ndsGS}.
  Context `{_memGS: !MemLib.memGS}.
  Import NDSNodeI.

  Section SPEC.
    Context (E: coPset).

    Definition N_nds_node : namespace := (nroot .@ "NDSNode.x").

    Definition inv_x_points_to (loc: Z) : iProp Σ :=
      inv 0 N_nds_node (∃ (v: τ{ ⇣nat }), loc ⤇ (Vint v))%SAT.

    Definition f_main_spec : fspec :=
      fspec_nds E
        (fspec_simple (λ (_: unit),
          (λ varg, ⌜varg = (tt↑↑)↑⌝,
           λ vret, ⌜vret = (tt↑↑)↑⌝)%I)).

    Definition f_spec : fspec :=
      fspec_nds E
        (fspec_virtual (λ (loc: Z),
             ((λ varg arg, ⌜varg = (tt↑↑) ∧ arg = ((Vint loc)↑↑)↑⌝ ∗ inv_x_points_to loc)%I,
              (λ vret ret, ⌜vret = (tt↑↑) ∧ ret = (tt↑↑)↑⌝)%I))).

    Definition sp : specmap :=
      {[fid NDSNodeHdr.f_main @ f_main_spec;
        fid NDSNodeHdr.f      @ f_spec]}.
  End SPEC.

  Definition f_main : SAny.t -> itree crisE SAny.t :=
    fun _ =>
      𝒩𝒴;;;
      'tid: nat <- ccallU NDSHdr.spawn (NDSNodeHdr.f.1, tt↑↑);; 𝒩𝒴;;; 𝒩𝒩;;;
      n <- trigger (Choose nat);; 𝒩𝒴;;;
      trigger (@IO _ unit "print" (Vint (Z.of_nat n)));;; 𝒩𝒴;;; 𝒩𝒩;;;
      Ret (tt↑↑).

  Definition f : SAny.t -> itree crisE SAny.t :=
    fun _ =>
      𝒩𝒴;;;
      n <- trigger (Choose nat);; 𝒩𝒴;;;
      trigger (@IO _ unit "print" (Vint (Z.of_nat n)));;; 𝒩𝒴;;; 𝒩𝒩;;;
      Ret (tt↑↑).

  Definition fnsems (E : coPset) : fnsemmap :=
    {[fid NDSNodeHdr.f_main # (msk_scp scopes msk_true, (fsp_some (f_main_spec E), cfunN (fntyp _ _) f_main));
      fid NDSNodeHdr.f      # (msk_scp scopes msk_true, (fsp_some (f_spec E), cfunN (fntyp _ _) f))]}.

  Program Definition smod E : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems E;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.
  
  Definition t sp := SMod.to_mod sp (smod ⊤).
End NDSNodeA. End NDSNodeA.
