Require Import CRIS.
From CRIS.celliocb Require Import CellioHeader CtxHeader.

Set Implicit Arguments.

(* This module is used to test the Cellio interface with a callback function. 
   The callback function is passed as a string to the set function, which allows 
   for dynamic behavior based on the provided callback. The get function retrieves 
   the value stored in the cell. *)

Module CellioI. Section CellioI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CellioHdr.mn].
  Definition v_cv := (CellioHdr.mn) ↯ "cv".

(* For convenience we use a string callback identifier here.
   The actual function-pointer implementation and Landin’s knot reasoning
   live in KnotI.v — please see that file. *)
  Definition set : string → itree crisE () :=
    λ cb,
      i <- ccallU CtxHdr.cb_t cb tt;;
      cput v_cv i;;;
      Ret tt.

  Definition get : () → itree crisE Z :=
    λ _,
      i <- cgetU v_cv;;
      Ret i.

  Definition fnsems : fnsemmap :=
    {[fid CellioHdr.set # ((msk_scp scopes msk_true), (None, cfunU CellioHdr.set_t set));
      fid CellioHdr.get # ((msk_scp scopes msk_true), (None, cfunU CellioHdr.get_t get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_cv # (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CellioI. End CellioI.
