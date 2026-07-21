Require Import CRIS.common.CRIS.
Require Import CRIS.scheduler.SchHeader.
From CRIS.scheduler Require Import NDS.NDSHeader.
From CRIS.hybrid_mem Require Import MemHdr.
From CRIS.scheduler Require Import example.NDSNodeHeader.

Set Implicit Arguments.

Module NDSNodeI. Section NDSNodeI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [NDSNODE].

  Definition f_main : SAny.t → itree crisE SAny.t :=
    λ _,
      'x: val <- ccallU MemHdr.alloc [Vint 1];; 𝒩𝒴;;;
      '_: val <- ccallU MemHdr.store [x; Vint 0];; 𝒩𝒴;;;
      'tid: nat <- ccallU NDSHdr.spawn (NDSNodeHdr.f.1, x↑↑);; 𝒩𝒴;;; 𝒩𝒩;;;
      'v: val <- ccallU MemHdr.load [x];; 𝒩𝒴;;;
      nx <- (vadd v (Vint 1))?;; 𝒩𝒴;;;
      '_: val <- ccallU MemHdr.store [x; nx];; 𝒩𝒴;;;
      trigger (@IO _ unit "print" v);;; 𝒩𝒴;;; 𝒩𝒩;;;
      Ret (tt↑↑).

  Definition f : SAny.t → itree crisE SAny.t :=
    λ arg,
      'x: val <- (arg↓↓)?;; 𝒩𝒴;;;
      'v: val <- ccallU MemHdr.load [x];; 𝒩𝒴;;;
      nx <- (vadd v (Vint 1))?;; 𝒩𝒴;;;
      '_: val <- ccallU MemHdr.store [x; nx];; 𝒩𝒴;;;
      trigger (@IO _ unit "print" v);;; 𝒩𝒴;;; 𝒩𝒩;;; 
      Ret (tt↑↑).

  Definition fnsems : fnsemmap :=
    {[fid NDSNodeHdr.f_main # (msk_real (msk_scp scopes msk_true), (None, cfunU NDSNodeHdr.f_main f_main));
      fid NDSNodeHdr.f      # (msk_real (msk_scp scopes msk_true), (None, cfunU NDSNodeHdr.f f))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End NDSNodeI. End NDSNodeI.
