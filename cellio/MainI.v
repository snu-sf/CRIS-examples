Require Import CRIS.
Require Import CellioHeader CtxHeader.

Set Implicit Arguments.

Module MainI. Section MainI.
  Context `{Σ: GRA}.

  Definition scopes := ["Main"].

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      ccallU (Y:=unit) CellioHdr.set tt;;;
      ccallU (Y:=unit) CtxHdr.foo tt;;;
      x <- ccallU (Y:=Z) CellioHdr.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.
  
  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(None, (false, wmask_all, scopes, (None, main)))].

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).
End MainI. End MainI.
