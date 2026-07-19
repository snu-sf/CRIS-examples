From CRIS.common Require Import CRIS.

Require Import ImpPrelude.
Require Import CellHeader.

Module CellI. Section CellI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (* Index of this Cell *)
  Variable idx : nat.

  (* Scopes and a member variable `cv` *)
  Definition scopes : list string := [CellHdr.mn idx].
  Definition v_cv := (CellHdr.mn idx) ↯ "cv".

  (* Implementations of get and set *)
  Definition get : unit -> itree crisE Z :=
    λ _,
      cv <- cgetU v_cv;;
      Ret cv.

  Definition set : Z -> itree crisE unit :=
    λ x,
      cput v_cv x;;;
      Ret ().

  Definition fnsems : fnsemmap :=
    {[fid (CellHdr.get idx) # (msk_real (msk_scp scopes msk_true), (None, cfunU (CellHdr.get idx) get));
      fid (CellHdr.set idx) # (msk_real (msk_scp scopes msk_true), (None, cfunU (CellHdr.set idx) set))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_cv # tt↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CellI. End CellI.
