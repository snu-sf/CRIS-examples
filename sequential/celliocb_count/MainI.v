From CRIS.common Require Import CRIS.
From CRIS.celliocb Require Import MainHeader CellioHeader CtxHeader.

Module MainI. Section MainI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["Main"].
  Definition v_count := "Main" ↯ "count".

  Definition input_cb : () -> itree crisE Z :=
    λ _,
      'count : Z <- cgetU v_count;;
      cput v_count (count + 1)%Z;;;
      Ret (7%Z).

  Definition main : Any.t -> itree crisE Any.t :=
    λ _,
      ccallU CellioHdr.set MainHdr.input_cb.1;;;
      ccallU CtxHdr.foo tt;;;
      x <- ccallU CellioHdr.get tt;;
      'count : Z <- cgetU v_count;;
      trigger (@IO _ unit "Print" (count, x));;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[fid MainHdr.input_cb #
        ((msk_scp scopes msk_true), (None, cfunU MainHdr.input_cb input_cb));
      entry # ((msk_scp scopes msk_true), (None, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_count # (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End MainI. End MainI.
