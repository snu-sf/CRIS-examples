Require Import CRIS.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.celliostk Require Import MainHeader CellioHeader CtxHeader.

Module MainI. Section MainI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition input_cb: () -> itree crisE Z :=
    λ _,
      trigger (@IO _ unit "Output_stdout" 42);;;
      i <- trigger (@IO _ Z "Input_db" tt);;
      Ret i.

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      'stk: val <- ccallU CellioHdr.new ();;
      i <- trigger (@IO _ Z "Input_stdin" tt);;
      'stk: val <- ITree.iter (λ '(i,stk),
        if (i <=? 0)%Z then Ret (inr stk)
        else
          'stk: val <- ccallU CellioHdr.push (fn_name MainHdr.input_cb, stk);;
           Ret (inl ((i - 1)%Z, stk))
        ) (i, stk);;
      ccallU CtxHdr.foo tt;;;
      ITree.iter (λ stk,
        '(x, stk): option Z * val <- ccallU CellioHdr.pop stk;;
        match x with
        | None => Ret (inr ())
        | Some z => trigger (@IO _ unit "Print" z);;; Ret (inl stk)
        end) stk;;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[fid MainHdr.input_cb     # ((msk_scp scopes msk_true), (None, cfunU MainHdr.input_cb input_cb));
      entry                    # ((msk_scp scopes msk_true), (None, main))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.
  
  Definition t := SMod.to_mod ∅ smod.
End MainI. End MainI.
