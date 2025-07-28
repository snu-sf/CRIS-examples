Require Import CRIS.
Require Import MaincbHeader CelliocbHeader CtxcbHeader.

Set Implicit Arguments.

Module MaincbI. Section MaincbI.
  Context `{Σ: GRA}.

  Definition scopes := ["Main"].

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
  
  Definition fnsems : fnsems_type :=
    [(Some MaincbHdr.input_stdin, (false, wmask_all, scopes, (None, input_stdin)));
     (Some MaincbHdr.input_db, (false, wmask_all, scopes, (None, input_db)));
     (MaincbHdr.main, (false, wmask_all, scopes, (None, main)))].

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End MaincbI. End MaincbI.

