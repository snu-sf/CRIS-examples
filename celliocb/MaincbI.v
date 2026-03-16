Require Import CRIS.
Require Import MaincbHeader CelliocbHeader CtxcbHeader.

Module MaincbI. Section MaincbI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition input_cb: Any.t -> itree crisE Any.t :=
    λ _,
      i <- trigger (@IO _ Z "Input_stdin" tt);;
      i <- trigger (@IO _ Z "Input_db" tt);;
      Ret i↑.

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      ccallU (Y:=unit) CelliocbHdr.set MaincbHdr.input_cb;;;
      trigger (Call CtxcbHdr.foo tt↑);;;
      x <- ccallU (Y:=Z) CelliocbHdr.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[fid MaincbHdr.input_cb     # ((msk_scp scopes msk_true), (None, input_cb));
      entry  # ((msk_scp scopes msk_true), (None, main))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.
  
  Definition t := SMod.to_mod ∅ smod.
End MaincbI. End MaincbI.

