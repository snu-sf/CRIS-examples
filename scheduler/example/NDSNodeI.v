Require Import CRIS.
Require Import SchHeader NDSHeader MemHdr.
Require Import NDSNodeHeader.

Set Implicit Arguments.

Module NDSNodeI. Section NDSNodeI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concGS}.

  Definition scopes : list string := [NDSNODE].

  Definition f_main : SAny.t → itree crisE SAny.t :=
    λ _,
      'x: val <- ccallU MemHdr.alloc [Vint 1];; 𝒩𝒴;;;
      '_: val <- ccallU MemHdr.store [x; Vint 0];; 𝒩𝒴;;;
      'tid: nat <- ccallU NDSHdr.spawn (NDSNodeHdr.f, x↑↑);; 𝒩𝒴;;; 𝒩𝒩;;;
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
    {[Some NDSNodeHdr.f_main := Some (msk_real (msk_scp scopes msk_true), (None, cfunU f_main));
      Some NDSNodeHdr.f      := Some (msk_real (msk_scp scopes msk_true), (None, cfunU f))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End NDSNodeI. End NDSNodeI.
