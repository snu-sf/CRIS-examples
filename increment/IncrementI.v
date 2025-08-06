Require Import CRIS.
Require Import ImpPrelude MemHeader SchHeader.
From CRIS.increment Require Import Header.

Module IncrementI. Section IncrementI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition increment : list val → itree crisE val :=
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

  Definition fnsems : fnsems_type :=
    [(Some IncrementHdr.increment, (false, wmask_all, scopes, (None, cfunU increment)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End IncrementI. End IncrementI.
