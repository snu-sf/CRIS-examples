Require Import CRIS.common.CRIS.
Require Import CRIS.scheduler.SchHeader RRSHeader.
Require Import MemHeader.
Require Import RRSNodeHeader.

Set Implicit Arguments.

Module RRSNodeI. Section RRSNodeI.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [RRSNODE].

  Definition f_main : SAny.t -> itree crisE SAny.t :=
    fun _ =>
      'x: val <- ccallU MemHdr.alloc [Vint 1];; ℛ𝒴;;;
      '_: val <- ccallU MemHdr.store [x; Vint 0];; ℛ𝒴;;;
      'tid1: nat <- ccallU RRSHdr.spawn (RRSNodeHdr.f.1, x↑↑);; ℛ𝒴;;;
      'tid2: nat <- ccallU RRSHdr.spawn (RRSNodeHdr.f.1, x↑↑);; ℛ𝒴;;; ℛℛ;;;
      Ret (tt↑↑)
  .

  Definition f : SAny.t -> itree crisE SAny.t :=
    fun arg =>
      'x: val <- (arg↓↓)?;; ℛ𝒴;;;
      'v: val <- ccallU MemHdr.load [x];; ℛ𝒴;;;
      'tid : nat <- ccallU RRSHdr.get_tid tt;; ℛ𝒴;;;
      o <- (vsub (Vint tid) v)?;; ℛ𝒴;;;
      nx <- (vadd v (Vint 1))?;; ℛ𝒴;;;
      '_: val <- ccallU MemHdr.store [x; nx];; ℛ𝒴;;;
      trigger (@IO _ unit "print" o);;; ℛ𝒴;;; ℛℛ;;; 
      Ret (tt↑↑)
  .
  
  Definition fnsems : fnsemmap :=
    {[fid RRSNodeHdr.f_main # (msk_real (msk_scp scopes msk_true), (None, cfunU RRSNodeHdr.f_main f_main));
      fid RRSNodeHdr.f      # (msk_real (msk_scp scopes msk_true), (None, cfunU RRSNodeHdr.f f))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End RRSNodeI. End RRSNodeI.
