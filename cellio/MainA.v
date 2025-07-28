Require Import CRIS.
Require Import CellioA CtxHeader CellioHeader.

Set Implicit Arguments.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_cellioG: !cellioG}.
                
  Definition scopes : list string := [].

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      'i: Z <- ccallU CtxHdr.input tt;;
      '_: unit <- ccallU CtxHdr.foo tt;;
      '_: unit <- trigger (IO "Print" i);;
      Ret tt↑.
  
  Definition fnsems : fnsems_type :=
    [(None, (true, wmask_all, scopes, (None, main)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := (cell 0)%I.

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp smod).

End MainA. End MainA.
