Require Import CRIS.
Require Import MutHeader MutMainHeader.

Set Implicit Arguments.

Module MutMainI. Section MutMainI.
  Context {Σ: GRA}.

  Definition scopes := ["MutMain"].

  (***
    main() := return f(10)
  ***)
  Definition mainF: () -> itree pmodE val :=
    fun _ =>
      'r: val <- ccallU MutHdr.mutf [Vint 10];;
      Ret r
  .

  Definition fnsems :=
    [(MutMainHdr.main, (wmask_all, scopes, cfunU mainF))].
  
  Program Definition Mod: PMod.t :=
  {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End MutMainI. End MutMainI.