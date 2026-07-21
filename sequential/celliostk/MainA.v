From CRIS.common Require Import CRIS.
From CRIS.celliostk Require Import CellioA MainI CtxHeader CellioHeader
  MainHeader.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !cellioGS}.
                
  Definition scopes : list string := [].

  Definition input_cb: () -> itree crisE Z := MainI.input_cb.

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      let stk: list Z := [] in
      i <- trigger (@IO _ Z "Input_stdin" tt);;
      'stk: list Z <- ITree.iter (λ '(i,stk),
        if (i <=? 0)%Z then Ret (inr stk)
        else
          'z: Z <- ccallU MainHdr.input_cb tt;;
           Ret (inl ((i - 1)%Z, z :: stk))
        ) (i, stk);;
      ccallU CtxHdr.foo tt;;;
      ITree.iter (λ stk,
        match stk with
        | [] => Ret (inr ())
        | z :: stk' => trigger (@IO _ unit "Print" z);;; Ret (inl stk')
        end) stk;;;
      Ret tt↑.
  
  Definition fnsems : fnsemmap :=
    {[fid MainHdr.input_cb     # ((msk_scp scopes msk_true), (None, cfunU MainHdr.input_cb input_cb));  
      entry # ((msk_scp scopes msk_true), (None, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End MainA. End MainA.
