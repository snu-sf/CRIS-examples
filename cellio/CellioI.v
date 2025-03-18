Require Import CRIS.

Require Import CellioHeader LibHeader.

Set Implicit Arguments.

Module CellioI. Section CellioI.
  Context `{Σ: GRA}.

  Definition scopes := [CellioName.mn].
  Definition v_cv := (CellioName.mn) ↯ "cv".

  Definition set: Any.t -> itree pmodE Any.t :=
    λ _,
      'i: Z <- ccallU LibName.input tt;;
      cput v_cv i;;;
      Ret tt↑.

  Definition get: Any.t -> itree pmodE Any.t :=
    λ _,
      i <- cgetU v_cv;;
      Ret (i:Z)↑.

  Definition fnsems :=
    [(CellioName.set, (scopes, set));
     (CellioName.get, (scopes, get))].

  Program Definition Mod: PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [(v_cv, (0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.
  
  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End CellioI. End CellioI.