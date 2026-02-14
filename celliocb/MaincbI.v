Require Import CRIS.
Require Import MaincbHeader CelliocbHeader CtxcbHeader.

Module MaincbI. Section MaincbI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition input_stdin: Any.t -> itree crisE Any.t :=
    λ _,
      i <- trigger (@IO _ Z "Input_stdin" tt);;
      Ret i↑.

  Definition input_db: Any.t -> itree crisE Any.t :=
    λ _,
      i <- trigger (@IO _ Z "Input_db" tt);;
      Ret i↑.

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      ccallU (Y:=unit) CelliocbHdr.set MaincbHdr.input_stdin ;;;
      i <- ccallU (Y:=Z) CelliocbHdr.get tt;;
      ccallU (Y:=unit) CtxcbHdr.foo i;;;
      ccallU (Y:=unit) CelliocbHdr.set MaincbHdr.input_db ;;;
      x <- ccallU (Y:=Z) CelliocbHdr.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[Some MaincbHdr.input_stdin  := Some ((msk_scp scopes msk_true), (None, input_stdin));
      Some MaincbHdr.input_db     := Some ((msk_scp scopes msk_true), (None, input_db));
      MaincbHdr.main         := Some ((msk_scp scopes msk_true), (None, main))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.
  
  Definition t := SMod.to_mod ∅ smod.
End MaincbI. End MaincbI.

