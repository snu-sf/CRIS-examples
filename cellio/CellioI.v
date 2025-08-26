Require Import CRIS.
Require Import CellioHeader CtxHeader.

Module CellioI. Section CellioI.
  Context `{Σ: GRA}.

  Definition scopes := [CellioHdr.mn].
  Definition v_cv := (CellioHdr.mn) ↯ "cv".

  Definition set: Any.t -> itree crisE Any.t :=
    λ _,
      'i : Z <- ccallU CtxHdr.input tt;;
      cput v_cv i;;;
      Ret tt↑.

  Definition get: Any.t -> itree crisE Any.t :=
    λ _,
      i <- cgetU v_cv;;
      Ret (i : Z)↑.

  Definition fnsems : fnsems_type :=
    [(Some CellioHdr.set, (false, wmask_all, scopes, (None, set)));
     (Some CellioHdr.get, (false, wmask_all, scopes, (None, get)))].

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_cv, (0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End CellioI. End CellioI.
