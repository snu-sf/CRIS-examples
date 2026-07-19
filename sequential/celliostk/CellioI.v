From CRIS.common Require Import CRIS.
From CRIS.imp_system Require Import mem.MemA.
From CRIS.celliostk Require Import CellioHeader CtxHeader.

Set Implicit Arguments.

(* This module is used to test the Cellio interface with a callback function. 
   The callback function is passed as a string to the set function, which allows 
   for dynamic behavior based on the provided callback. The get function retrieves 
   the value stored in the cell. *)

Module CellioI. Section CellioI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CellioHdr.mn].
  Definition v_cv := (CellioHdr.mn) ↯ "cv".

  Definition new: unit -> itree crisE val :=
    λ _, Ret Vnullptr.

(* For convenience we use a string callback identifier here.
   The actual function-pointer implementation and Landin’s knot reasoning
   live in KnotI.v — please see that file. *)

  Definition push: string * val -> itree crisE val :=
    λ '(cb,p),
      'i: Z <- ccallU (fnsig cb CtxHdr.cb_t) tt;;
      'pnew: val <- ccallU MemHdr.alloc [Vint 2];;
      'pnew1: val <- (vadd pnew (Vint 8))?;;
      '_: val <- ccallU MemHdr.store [pnew; Vint i];;
      '_: val <- ccallU MemHdr.store [pnew1; p];;
      Ret pnew.

  Definition pop: val -> itree crisE (option Z * val) :=
    λ p,
      if decide (p = Vnullptr) then Ret (None, p)
      else
        'p1: val <- (vadd p (Vint 8))?;;
        'i: val <- ccallU MemHdr.load [p];;
        'pnew: val <- ccallU MemHdr.load [p1];;
        '_: val <- ccallU MemHdr.free [p];;
        '_: val <- ccallU MemHdr.free [p1];;
        'z: Z  <- (unint i)?;;
        Ret (Some z, pnew).

  Definition fnsems : fnsemmap :=
    {[fid CellioHdr.new  # (msk_scp scopes msk_true, (None, cfunU CellioHdr.new new));
      fid CellioHdr.push # (msk_scp scopes msk_true, (None, cfunU CellioHdr.push push));
      fid CellioHdr.pop  # (msk_scp scopes msk_true, (None, cfunU CellioHdr.pop pop))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CellioI. End CellioI.
