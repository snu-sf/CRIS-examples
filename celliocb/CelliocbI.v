Require Import CRIS.

Require Import CelliocbHeader.

Set Implicit Arguments.

(* This module is used to test the Cellio interface with a callback function. 
   The callback function is passed as a string to the set function, which allows 
   for dynamic behavior based on the provided callback. The get function retrieves 
   the value stored in the cell. *)

Module CelliocbI. Section CelliocbI.
  Context `{Σ: GRA}.

  Definition scopes := [CelliocbHdr.mn].
  Definition v_cv := (CelliocbHdr.mn) ↯ "cv".

(* For convenience we use a string callback identifier here.
   The actual function-pointer implementation and Landin’s knot reasoning
   live in KnotI.v — please see that file. *)
  Definition set: string -> itree crisE unit :=
    λ cb,
      'i: Z <- ccallU cb tt;;
      cput v_cv i;;;
      Ret tt.

  Definition get: Any.t -> itree crisE Any.t :=
    λ _,
      i <- cgetU v_cv;;
      Ret (i:Z)↑.

  Definition fnsems : fnsems_type :=
    [(Some CelliocbHdr.set, (false, wmask_all, scopes, (None, cfunU set)));
     (Some CelliocbHdr.get, (false, wmask_all, scopes, (None, get)))].

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_cv, (0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End CelliocbI. End CelliocbI.
