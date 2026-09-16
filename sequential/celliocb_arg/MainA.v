From CRIS.common Require Import CRIS.
From CRIS.celliocb_arg Require Import CellioA CtxHeader CellioHeader MainHeader.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !cellioGS}.

  Definition scopes : list string := ["Main"].
  Definition v_count := "Main" ↯ "count".

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ _, cell 0),
       (λ _, True)
      )
    )%I.

  (* ptr is a logical state key, not an imp_system memory pointer. *)
  Definition input_cb : key -> itree crisE Z :=
    λ ptr,
      'count : Z <- cgetU ptr;;
      cput ptr (count + 1)%Z;;;
      Ret (7%Z).

  Definition main : Any.t -> itree crisE Any.t :=
    λ _,
      'i : Z <- ccallU MainHdr.input_cb v_count;;
      ccallU CtxHdr.foo tt;;;
      'count : Z <- cgetU v_count;;
      trigger (@IO _ unit "Print" (count, i));;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[fid MainHdr.input_cb #
        ((msk_scp scopes msk_true), (None, cfunU MainHdr.input_cb input_cb));
      entry # ((msk_scp scopes msk_true), (fsp_some main_spec, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_count # (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End MainA. End MainA.
