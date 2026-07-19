From CRIS.common Require Import CRIS.
From CRIS.cellio Require Import CellioHeader CtxHeader.

Module CellioI. Section CellioI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CellioHdr.mn].
  Definition v_cv := (CellioHdr.mn) ↯ "cv".

  Definition set: () -> itree crisE () :=
    λ _,
      'i : Z <- ccallU CtxHdr.input tt;;
      cput v_cv i;;;
      Ret tt.

  Definition get: () -> itree crisE Z :=
    λ _,
      i <- cgetU v_cv;;
      Ret i.

  Definition fnsems : fnsemmap :=
    {[fid CellioHdr.set # (msk_real (msk_scp scopes msk_true), (fsp_none, cfunU CellioHdr.set set));
      fid CellioHdr.get # (msk_real (msk_scp scopes msk_true), (fsp_none, cfunU CellioHdr.get get))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_cv # (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CellioI. End CellioI.
