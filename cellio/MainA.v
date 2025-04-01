Require Import CRIS.
Require Import CellioA CtxHeader CellioHeader MainHeader.

Set Implicit Arguments.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  Definition scopes := [MainHdr.mn].

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      trigger (Assume (cell 0));;;
      'i: Z <- ccallU CtxHdr.input tt;;
      '_: unit <- ccallU CtxHdr.foo tt;;
      '_: unit <- trigger (IO "Print" i);;
      Ret tt↑.
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(MainHdr.main, (scopes, mk_specbody fspec_trivial main))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.

  Definition InitRes : Σ := ε.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod emp sp Mod).

End MainA. End MainA.
