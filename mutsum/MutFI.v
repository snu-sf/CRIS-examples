Require Import CRIS.
Require Import MutHeader.

Set Implicit Arguments.

Module MutFI. Section MutFI.
  Context `{!crisG Σ Γ α β τ Hinv Hsub, _CONC: !concGS}.

  Definition scopes := ["MutF"].

  (***
    f(n) := if (n == 0) then 0 else (n + g(n - 1))
  ***)
  Definition fF: list val -> itree crisE val :=
    fun varg =>
      'n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if dec n 0%Z
      then Ret (Vint 0)
      else (
        m <- ccallU MutHdr.mutg [Vint (n - 1)];;
        r <- (vadd (Vint n) m)?;;
        Ret r
      )
  .

  Definition fnsems : fnsemmap :=
    {[Some MutHdr.mutf := Some (msk_scp scopes msk_true, (None, cfunU fF))]}.
  
  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End MutFI. End MutFI.
