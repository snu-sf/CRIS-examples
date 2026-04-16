Require Import CRIS.
From CRIS.celliocb Require Import MainHeader CellioHeader CtxHeader.

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
      ccallU CellioHdr.set MainHdr.input_cb.1;;;
      ccallU CtxHdr.foo tt;;;
      x <- ccallU CellioHdr.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[fid MainHdr.input_cb     # ((msk_scp scopes msk_true), (None, cfunU MainHdr.input_cb input_cb));
      entry  # ((msk_scp scopes msk_true), (None, main))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.
  
  Definition t := SMod.to_mod ∅ smod.
End MainI. End MainI.
