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

  (* 이게 콜백이 맞을까? 의미적으로... *)
  Definition set: string -> itree hmodE unit :=
    λ cb,
      'i: Z <- ccallU cb tt;;
      cput v_cv i;;;
      Ret tt.

  Definition get: Any.t -> itree hmodE Any.t :=
    λ _,
      i <- cgetU v_cv;;
      Ret (i:Z)↑.

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some CelliocbHdr.set, (false, wmask_all, scopes, (None, cfunU set)));
     (Some CelliocbHdr.get, (false, wmask_all, scopes, (None, get)))].

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_cv, (0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).
End CelliocbI. End CelliocbI.
