Require Import CRIS.
Require Import MutHeader.

Set Implicit Arguments.

Module MutFI. Section MutFI.

  Context {Σ: GRA}.

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

  Definition fnsems : fnsems_type :=
    [(Some MutHdr.mutf, (false, wmask_all, scopes, (None, cfunU fF)))].
  
  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End MutFI. End MutFI.