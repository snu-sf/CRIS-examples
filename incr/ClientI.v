Require Import CRIS.
Require Import ImpPrelude MemHeader SchHeader.
Require Import IncrHeader.

Module ClientI. Section ClientI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition thread : list val → itree crisE unit :=
    λ arg,
      𝒴;;; '_ : val <- ccallU IncrHdr.incr arg;;
      𝒴;;; '_ : val <- ccallU IncrHdr.incr arg;;
      𝒴;;; Ret tt.

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;; 'ptr_raw : val <- ccallU MemHdr.alloc [Vint 1%Z];;
      𝒴;;; bofs <- (pargs [Tptr] [ptr_raw])?;;
      𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr bofs; Vint 0%Z];;
      𝒴;;; tid1 <- Sch.spawn (ClientHdr.thread, [Vptr bofs]↑↑);;
      𝒴;;; tid2 <- Sch.spawn (ClientHdr.thread, [Vptr bofs]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; 'v_raw : val <- ccallU MemHdr.load [Vptr bofs];;
      𝒴;;; 'v : Z <- (pargs [Tint] [v_raw])?;;
      𝒴;;; '_ : val <- trigger (IO "OUT" v);;
      𝒴;;; Ret (tt↑).

  Definition fnsems : fnsemmap :=
    {[fid ClientHdr.thread # (msk_real (msk_scp scopes msk_true), (None, cfunU (sfunU thread)));
      entry # (msk_real (msk_scp scopes msk_true), (None, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End ClientI. End ClientI.
