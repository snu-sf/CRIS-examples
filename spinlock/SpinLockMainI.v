Require Import CRIS.
Require Import ImpPrelude SchHeader MemHeader SpinLockHeader SpinLockMainHeader.

(* Implementation of an example user module that uses spinlock library *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockMainI. Section SpinLockMainI.
  Definition scopes : list string := [].

  Definition main : unit → itree pmodE unit :=
    λ _,
      𝒴;;; 'v : val <- ccallU MemName.alloc [Vint 1];;
      𝒴;;; '_ : val <- ccallU MemName.store [v; Vint 0];;
      𝒴;;; 'l : val <- ccallU SpinLockName.newlock ([] : list val);;
      𝒴;;; 't1 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; 't2 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; '_ : SAny.t <- Sch.join t1;;
      𝒴;;; '_ : SAny.t <- Sch.join t2;;
      𝒴;;; '_ : val <- ccallU SpinLockName.acquire [l];;
      𝒴;;; 'x : val <- ccallU MemName.load [v];;
      𝒴;;; 'x : Z <- (pargs [Tint] [x])?;;
      𝒴;;; '_ : val <- ccallU SpinLockName.release [l];;
      𝒴;;; '_ : unit <- trigger (IO "printf" x);;
      𝒴;;; Ret tt.

  Definition incr : list val → itree pmodE val :=
    λ arg,
      𝒴;;; '(lb, lo, (vb, vo)) : (mblock * ptrofs * (mblock * ptrofs)) <- (pargs [Tptr; Tptr] arg)?;;
      let l := Vptr lb lo in
      let v := Vptr vb vo in
      𝒴;;; '_ : val <- ccallU SpinLockName.acquire [l];;
      𝒴;;; 'x : val <- ccallU MemName.load [v];;
      𝒴;;; 'x : Z <- (pargs [Tint] [x])?;;
      𝒴;;; '_ : val <- ccallU MemName.store [v; Vint (x + 1)];;
      𝒴;;; '_ : val <- ccallU SpinLockName.release [l];;
      𝒴;;; Ret Vundef.

  Definition fnsems :=
    [(SpinLockMainName.main, (scopes, cfunU main));
     (SpinLockMainName.incr, (scopes, cfunU (sfunU incr)))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t {Σ : GRA} : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End SpinLockMainI. End SpinLockMainI.
