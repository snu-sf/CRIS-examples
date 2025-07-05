Require Import CRIS.
Require Import MaincbHeader CelliocbHeader CtxcbHeader.

Set Implicit Arguments.

Module MaincbI. Section MaincbI.
  Context `{Σ: GRA}.

  Definition scopes := ["Main"].

  (* Is it Right : input in MainI ?? *)
  Definition input: Any.t -> itree hmodE Any.t :=
    λ _,
      i <- trigger (@IO _ Z "Input" tt);;
      Ret i↑.

  (* Is it need foo in this example?? *)
  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      ccallU (Y:=unit) CelliocbHdr.set MaincbHdr.input;;;
      ccallU (Y:=unit) CtxcbHdr.foo tt;;;
      x <- ccallU (Y:=Z) CelliocbHdr.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.
  
  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some MaincbHdr.input, (false, wmask_all, scopes, (None, input)));
     (MaincbHdr.main, (false, wmask_all, scopes, (None, main)))].

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).
End MaincbI. End MaincbI.

