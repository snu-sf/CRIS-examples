Require Import CRIS.

Require Import ImpPrelude.
Require Import CellHeader.

Set Implicit Arguments.

Module CellI. Section CellI.
  Context `{Σ : GRA}.

  (* Index of this Cell *)
  Variable idx : nat.

  (* Scopes and a member variable `cv` *)
  Definition scopes := [CellHdr.mn idx].
  Definition v_cv := (CellHdr.mn idx) ↯ "cv".

  (* Implementations of get and set *)
  Definition get : unit -> itree crisE Z :=
    λ _,
      cv <- cgetU v_cv;;
      Ret cv.

  Definition set : Z -> itree crisE unit :=
    λ x,
      cput v_cv x;;;
      Ret ().

  Definition fnsems : fnsems_type :=
    [(Some (CellHdr.get idx), (false, wmask_all, scopes, (None, cfunU get)));
     (Some (CellHdr.set idx), (false, wmask_all, scopes, (None, cfunU set)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_cv,tt↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End CellI. End CellI.
