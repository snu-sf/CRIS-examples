Require Import CRIS.
Require Import LockHeader.
Require Import ImpPrelude SchHeader MemHeader.

(* Implementation of the spinlock library *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockI. Section SpinLockI.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS}.

  Definition scopes : list string := [].

  Definition newlock : list val → itree crisE val :=
    λ _,
      𝒴;;; 'loc : val <- ccallU MemHdr.alloc [Vint 1];;
      𝒴;;; '_ : val <- ccallU MemHdr.store [loc; Vint 0];;
      𝒴;;; Ret loc.

  Definition acquire : list val → itree crisE val :=
    λ x,
      (iterC
        (λ _,
          𝒴;;; 'b_raw : val <- ccallU MemHdr.cas (x ++ [Vint 0; Vint 1]);;
          𝒴;;; 'b : Z <- (pargs [Tint] [b_raw])?;;
          𝒴;;;
            if (decide (b = 1)) then Ret (inl tt)
            else if (decide (b = 0)) then Ret (inr tt)
            else triggerUB
        ) tt);;;
      𝒴;;; Ret Vundef.

  Definition release : list val → itree crisE val :=
    λ x,
      𝒴;;; '_ : val <- ccallU MemHdr.store (x ++ [Vint 0]);;
      𝒴;;; Ret Vundef.

  Definition fnsems : fnsemmap :=
    {[Some SpinLockHdr.newlock := Some (msk_real (msk_scp scopes msk_true), (None, cfunU newlock));
      Some SpinLockHdr.acquire := Some (msk_real (msk_scp scopes msk_true), (None, cfunU acquire));
      Some SpinLockHdr.release := Some (msk_real (msk_scp scopes msk_true), (None, cfunU release))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End SpinLockI. End SpinLockI.
