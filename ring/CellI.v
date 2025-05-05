Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader.
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
  Definition get : unit -> itree pmodE Z :=
    λ _,
      cv <- cgetU v_cv;;
      Ret cv.

  Definition set : Z -> itree pmodE unit :=
    λ x,
      cput v_cv x;;;
      Ret ().

  Definition fnsems :=
    [(CellHdr.get idx, (wmask_all, scopes, cfunU get));
     (CellHdr.set idx, (wmask_all, scopes, cfunU set))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [(v_cv,tt↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End CellI. End CellI.
