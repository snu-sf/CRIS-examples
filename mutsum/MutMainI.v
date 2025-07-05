Require Import CRIS.
Require Import MutHeader.

Set Implicit Arguments.

Module MutMainI. Section MutMainI.
  Context {Σ: GRA}.

  Definition scopes := ["MutMain"].

  (***
    main() := return f(10)
  ***)
  Definition mainF: Any.t -> itree hmodE Any.t :=
    fun _ =>
      'r: val <- ccallU MutHdr.mutf [Vint 10];;
      Ret (r↑)
  .

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(None, (false, wmask_all, scopes, (None, mainF)))].
  
  Program Definition Mod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).
End MutMainI. End MutMainI.