Require Import CRIS.
Require Import CelliocbA CtxcbHeader CelliocbHeader MaincbHeader.

Set Implicit Arguments.

Module MaincbA. Section MaincbA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{_celliocbG: !celliocbG}.
                
  Definition scopes := ["Main"].

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit,
          ((λ arg, cell 0),
           (λ ret, emp))
    )%I.

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      'i: Z <- trigger (@IO _ Z "Input" tt);;
      '_: unit <- ccallU CtxcbHdr.foo tt;;
      '_: unit <- trigger (IO "Print" i);;
      Ret tt↑.
  
  Definition fnsems :=
    [(MaincbHdr.main, (true, wmask_all, scopes, (Some main_spec, main)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod sp Mod).

End MaincbA. End MaincbA.
