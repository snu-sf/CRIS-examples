Require Import CRIS.
From CRIS.spinlock_ia Require Import Header.
Require Import ImpPrelude SchHeader MemHeader.

(* Implementation of an example user module that uses spinlock library *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockMainI. Section SpinLockMainI.
  Context `{Σ: GRA}.
                        
  Definition scopes : list string := [].

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;; 'v : val <- ccallU MemHdr.alloc [Vint 1];;
      𝒴;;; '_ : val <- ccallU MemHdr.store [v; Vint 0];;
      𝒴;;; 'l : val <- ccallU SpinLockHdr.newlock ([] : list val);;
      𝒴;;; 't1 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; 't2 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; '_ : SAny.t <- Sch.join t1;;
      𝒴;;; '_ : SAny.t <- Sch.join t2;;
      𝒴;;; '_ : val <- ccallU SpinLockHdr.acquire [l];;
      𝒴;;; 'x : val <- ccallU MemHdr.load [v];;
      𝒴;;; 'x : Z <- (pargs [Tint] [x])?;;
      𝒴;;; '_ : val <- ccallU SpinLockHdr.release [l];;
      𝒴;;; '_ : unit <- trigger (IO "printf" x);;
      𝒴;;; Ret tt↑.

  Definition incr : list val → itree crisE val :=
    λ arg,
      𝒴;;; '(l, v): _ <- (pargs [Tptr; Tptr] arg)?;;
      𝒴;;; '_ : val <- ccallU SpinLockHdr.acquire [Vptr l];;
      𝒴;;; 'x : val <- ccallU MemHdr.load [Vptr v];;
      𝒴;;; 'x : Z <- (pargs [Tint] [x])?;;
      𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr v; Vint (x + 1)];;
      𝒴;;; '_ : val <- ccallU SpinLockHdr.release [Vptr l];;
      𝒴;;; Ret Vundef.

  Definition fnsems : fnsems_type :=
    [(None, (false, wmask_all, scopes, (None, main)));
     (Some SpinLockMainHdr.incr, (false, wmask_all, scopes, (None, cfunU (sfunU incr))))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End SpinLockMainI. End SpinLockMainI.
