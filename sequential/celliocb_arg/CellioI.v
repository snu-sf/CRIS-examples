From CRIS.common Require Import CRIS.
From CRIS.celliocb_arg Require Import CellioHeader CtxHeader.

Set Implicit Arguments.

Module CellioI. Section CellioI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CellioHdr.mn].
  Definition v_cv := CellioHdr.mn ↯ "cv".

  Definition set : string * key -> itree crisE () :=
    λ '(cb, arg),
      i <- ccallU (fnsig cb CtxHdr.cb_t) arg;;
      cput v_cv i;;;
      Ret tt.

  Definition get : () -> itree crisE Z :=
    λ _,
      i <- cgetU v_cv;;
      Ret i.

  Definition fnsems : fnsemmap :=
    {[fid CellioHdr.set #
        (msk_scp scopes msk_true, (None, cfunU CellioHdr.set set));
      fid CellioHdr.get #
        (msk_scp scopes msk_true, (None, cfunU CellioHdr.get get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_cv # (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CellioI. End CellioI.
