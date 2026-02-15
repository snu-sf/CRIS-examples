Require Import CRIS.

Require Import MutHeader.

Set Implicit Arguments.

Module MutGI. Section MutGI.
  Context `{!crisG Σ Γ α β τ Hinv Hsub}.

  Definition scopes := ["MutG"].

  (***
    g(n) := if (n == 0) then 0 else (n + f(n - 1))
  ***)
  Definition gF: list val -> itree crisE val :=
    fun varg =>
      'n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if dec n 0%Z
      then Ret (Vint 0)
      else (
        m <- ccallU MutHdr.mutf [Vint (n - 1)];;
        r <- (vadd (Vint n) m)?;;
        Ret r
      )
  .

  Definition fnsems : fnsemmap :=
    {[fid MutHdr.mutg # (msk_scp scopes msk_true, (None, cfunU gF))]}.
  
  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End MutGI. End MutGI.
