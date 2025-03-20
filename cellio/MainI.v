Require Import CRIS.
Require Import MainHeader CellioHeader LibHeader.

Set Implicit Arguments.

Module MainI. Section MainI.
  Context `{Σ: GRA}.

  Definition scopes := [MainHdr.mn].

  Definition main: Any.t -> itree pmodE Any.t :=
    λ _,
      ccallU (Y:=unit) CellioHdr.set tt;;;
      ccallU (Y:=unit) LibHdr.foo tt;;;
      x <- ccallU (Y:=Z) CellioHdr.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.
  
  Definition fnsems :=
    [(MainHdr.main, (scopes, main))].

  Program Definition Mod: PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End MainI. End MainI.
