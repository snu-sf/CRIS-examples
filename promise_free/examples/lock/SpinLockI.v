(* Require Import CRIS.
Require Import SchHeader PFMemHeader PFMemUser HistoryRA.
Require Import Val.

Module SpinLockHdr.
  Definition newlock := "newlock".
  Definition acquire := "acquire".
  Definition release := "release".
End SpinLockHdr.

Module SpinLockI. Section SpinLockI.
  Context `{Σ : GRA}.
  Definition scopes : list string := [].

  Definition newlock : () → itree hmodE Val.t :=
    λ _,
      𝒴;;; v <- PFMem.alloc 1%Z;; loc <- parse_loc v;;
      𝒴;;; PFMem.write (loc >> 0, Val.Vnum 0, Ordering.na);;;
      𝒴;;; Ret (Val.Vptr loc).

  Definition acquire : Val.t → itree hmodE Val.t :=
    λ arg,
      loc <- parse_loc arg;;
      iterC (λ _,
        𝒴;;;
          ret <- PFMem.cas (loc, Val.zero, Val.one, Ordering.acqrel, Ordering.acqrel);;
          ret <- parse_num ret;;
        𝒴;;;
          if (decide (ret = 0)) then Ret (inr (Val.zero))
          else Ret (inl tt)
      ) ().

  Definition release : Val.t → itree hmodE Val.t :=
    λ arg,
      𝒴;;;
        loc <- parse_loc arg;;
        ret <- PFMem.write (loc, Val.zero, Ordering.acqrel);;
      𝒴;;; Ret ret.

  Definition fnsems :=
    [(SpinLockHdr.newlock, (wmask_all, scopes, cfunU newlock));
     (SpinLockHdr.acquire, (wmask_all, scopes, cfunU acquire));
     (SpinLockHdr.release, (wmask_all, scopes, cfunU release))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End SpinLockI. End SpinLockI. *)