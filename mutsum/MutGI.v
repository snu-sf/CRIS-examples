Require Import CRIS.

Require Import MutHeader.

Set Implicit Arguments.

Module MutGI. Section MutGI.
  Context {Σ: GRA}.

  Definition scopes := ["MutG"].

  (***
    g(n) := if (n == 0) then 0 else (n + f(n - 1))
  ***)
  Definition gF: list val -> itree hmodE val :=
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

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some MutHdr.mutg, (false, wmask_all, scopes, (None, cfunU gF)))].
  
  Program Definition Mod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).
End MutGI. End MutGI.