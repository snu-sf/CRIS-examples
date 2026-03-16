Require Import CRIS.
Require Import CelliocbA CtxcbHeader CelliocbHeader MaincbHeader.

Module MaincbA. Section MaincbA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !celliocbGS}.
                
  Definition scopes : list string := [].

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit, 
      ((λ arg, (cell 0)), 
       (λ ret, (True))
      )
    )%I.

  Definition input_cb: Any.t -> itree crisE Any.t :=
    λ _,
      i <- trigger (@IO _ Z "Input_stdin" tt);;
      i <- trigger (@IO _ Z "Input_db" tt);;
      Ret i↑.

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      'i: Z <- ccallU MaincbHdr.input_cb tt;;
      trigger (Call CtxcbHdr.foo tt↑);;;
      trigger (@IO _ unit "Print" i);;;
      Ret tt↑.
  
  Definition fnsems : fnsemmap :=
    {[fid MaincbHdr.input_cb     # ((msk_scp scopes msk_true), (None, input_cb));  
      entry # ((msk_scp scopes msk_true), (fsp_some main_spec, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End MaincbA. End MaincbA.
