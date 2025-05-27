Require Import CRIS.
Require Import MutHeader.

Set Implicit Arguments.

Module MutFI. Section MutFI.

  Context {Σ: GRA}.

  Definition scopes := ["MutF"].

  (***
    f(n) := if (n == 0) then 0 else (n + g(n - 1))
  ***)
  Definition fF: list val -> itree hmodE val :=
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

  Definition fnsems :=
    [(MutHdr.mutf, (wmask_all, scopes, cfunU fF))].
  
  Program Definition Mod: PMod.t :=
  {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End MutFI. End MutFI.