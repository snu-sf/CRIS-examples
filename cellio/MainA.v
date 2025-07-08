Require Import CRIS.
Require Import CellioA CtxHeader CellioHeader.

Set Implicit Arguments.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{_cellioG: !cellioG}.
                
  Definition scopes := ["Main"].

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      'i: Z <- ccallU CtxHdr.input tt;;
      '_: unit <- ccallU CtxHdr.foo tt;;
      '_: unit <- trigger (IO "Print" i);;
      Ret tt↑.
  
  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(None, (true, wmask_all, scopes, (None, main)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := (cell 0)%I.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod sp Mod).

End MainA. End MainA.
