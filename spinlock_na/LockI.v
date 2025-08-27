Require Import CRIS.
From CRIS.spinlock_na Require Import Header.
Require Import ImpPrelude SchHeader MemHeader.

(* Implementation of the spinlock library *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockI. Section SpinLockI.
  Context {Σ : GRA}.

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

  Definition fnsems : fnsems_type :=
  [(Some SpinLockHdr.newlock, (false, wmask_all, scopes, (None, cfunU newlock)));
   (Some SpinLockHdr.acquire, (false, wmask_all, scopes, (None, cfunU acquire)));
   (Some SpinLockHdr.release, (false, wmask_all, scopes, (None, cfunU release)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).

End SpinLockI. End SpinLockI.
