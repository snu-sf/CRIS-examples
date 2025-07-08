Require Import CRIS.
Require Import CelliocbA CtxcbHeader CelliocbHeader MaincbHeader.

Set Implicit Arguments.

Module MaincbA. Section MaincbA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{_celliocbG: !celliocbG}.
                
  Definition scopes := ["Main"].

  Definition main: Any.t -> itree hmodE Any.t :=
    λ _,
      'i: Z <- trigger (@IO _ Z "Input_stdin" tt);;
      ccallU (Y:=unit) CtxcbHdr.foo i;;;
      'x: Z <- trigger (@IO _ Z "Input_db" tt);; 
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.
  
  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(MaincbHdr.main, (true, wmask_all, scopes, (None, main)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := cell 0.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod sp Mod).

End MaincbA. End MaincbA.
