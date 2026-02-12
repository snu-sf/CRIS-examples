Require Import CRIS.
Require Import MutHeader.

Set Implicit Arguments.

Module MutMainI. Section MutMainI.
  Context `{!crisG Σ Γ α β τ Hinv Hsub, !concGS}.

  Definition scopes := ["MutMain"].

  (***
    main() := return f(10)
  ***)
  Definition mainF: Any.t -> itree crisE Any.t :=
    fun _ =>
      'r: val <- ccallU MutHdr.mutf [Vint 10];;
      Ret (r↑)
  .

  Definition fnsems : fnsemmap :=
    {[None := Some (msk_scp scopes msk_true, (None, mainF))]}.
  
  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End MutMainI. End MutMainI.
