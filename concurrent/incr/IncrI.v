Require Import CRIS.common.CRIS.
Require Import ImpPrelude MemHeader.
From CRIS.scheduler Require Import SchHeader Atomic.
Require Export IncrHeader.

Module IncrI. Section IncrI.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.

  Definition scopes : list string := [].

  Definition incr : list val → itree crisE val :=
    λ arg,
      𝒴;;; bofs <- (pargs [Tptr] arg)?;;
      𝒴;;;
        iterC (λ _ : unit,
          𝒴;;; 'v_raw : val <- ccallU MemHdr.load [Vptr bofs];;
          𝒴;;; 'v : Z <- (pargs [Tint] [v_raw])?;;
          𝒴;;; 's_raw : val <- ccallU MemHdr.cas [Vptr bofs; Vint v; Vint (v + 1)];;
          𝒴;;; 's : Z <- (pargs [Tint] [s_raw])?;;
          𝒴;;;
            if (decide (s = v))
            then Ret (inr (Vint v))
            else Ret (inl tt)
        ) ().

  Definition fnsems : fnsemmap :=
    {[fid IncrHdr.incr # (msk_scp scopes msk_true, (None, cfunU imp_fun_t incr))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End IncrI. End IncrI.
