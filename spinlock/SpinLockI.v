Require Import CRIS.
Require Import ImpPrelude SchHeader MemHeader SpinLockHeader.

(* Implementation of the spinlock library *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockI. Section SpinLockI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition newlock : list val → itree pmodE val :=
    λ _,
      𝒴;;; 'loc : val <- ccallU MemHdr.alloc [Vint 1];;
      𝒴;;; '_ : val <- ccallU MemHdr.store [loc; Vint 0];;
      𝒴;;; Ret loc.

  Definition acquire : list val → itree pmodE val :=
    λ x,
      (ITree.iter
        (λ _,
          𝒴;;; 'b_raw : val <- ccallU MemHdr.cas (x ++ [Vint 0; Vint 1]);;
          𝒴;;; 'b : Z <- (pargs [Tint] [b_raw])?;;
          𝒴;;;
            if (decide (b = 0)) then Ret (inl tt)
            else if (decide (b = 1)) then Ret (inr tt)
            else triggerUB
        ) tt);;;
      𝒴;;; Ret Vundef.

  Definition release : list val → itree pmodE val :=
    λ x,
      𝒴;;; '_ : val <- ccallU MemHdr.store (x ++ [Vint 0]);;
      𝒴;;; Ret Vundef.

  Definition fnsems :=
    [(SpinLockHdr.newlock, (scopes, cfunU newlock));
     (SpinLockHdr.acquire, (scopes, cfunU acquire));
     (SpinLockHdr.release, (scopes, cfunU release))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End SpinLockI. End SpinLockI.
