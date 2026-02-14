Require Import CRIS.
Require Import CelliocbHeader CtxcbHeader.

Set Implicit Arguments.

(* This module is used to test the Cellio interface with a callback function. 
   The callback function is passed as a string to the set function, which allows 
   for dynamic behavior based on the provided callback. The get function retrieves 
   the value stored in the cell. *)

Module CelliocbI. Section CelliocbI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CelliocbHdr.mn].
  Definition v_cv := (CelliocbHdr.mn) ↯ "cv".

(* For convenience we use a string callback identifier here.
   The actual function-pointer implementation and Landin’s knot reasoning
   live in KnotI.v — please see that file. *)
  Definition set : string → itree crisE unit :=
    λ cb,
      'i: Z <- ccallU cb tt;;
      cput v_cv i;;;
      Ret tt.

  Definition get : Any.t → itree crisE Any.t :=
    λ _,
      i <- cgetU v_cv;;
      Ret (i : Z)↑.


  Definition fnsems : fnsemmap :=
    {[Some CelliocbHdr.set := Some ((msk_scp scopes msk_true), (None, cfunU set));
      Some CelliocbHdr.get := Some ((msk_scp scopes msk_true), (None, get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_cv := Some (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CelliocbI. End CelliocbI.
