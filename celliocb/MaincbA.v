Require Import CRIS.
Require Import CelliocbA CtxcbHeader CelliocbHeader MaincbHeader.

Module MaincbA. Section MaincbA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !celliocbGS}.
                
  Definition scopes : list string := [].

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit, 
      ((λ arg, (cell 0)), 
       (λ ret, (True))
      )
    )%I.

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      'i: Z <- trigger (@IO _ Z "Input_stdin" tt);;
      ccallU (Y:=unit) CtxcbHdr.foo i;;;
      'x: Z <- trigger (@IO _ Z "Input_db" tt);; 
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.
  
  Definition fnsems : fnsemmap :=
    {[MaincbHdr.main := Some ((msk_scp scopes msk_true), (fsp_some main_spec, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := cell 0.

  Definition t sp := SMod.to_mod sp smod.
End MaincbA. End MaincbA.
