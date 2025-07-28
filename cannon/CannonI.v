Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader.

Set Implicit Arguments.

Module CannonI. Section CannonI.
  Local Open Scope string_scope.

  Context `{Σ: GRA}.

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv". (* local variable *)

  Definition div (n m : Z) : option Z :=
    if Z_zerop m then None else Some (Z.div n m).

  Definition fire: list val -> itree crisE Z :=
    λ _,
      powder <- cgetU v_lv;;
      r <- (div 1 powder)?;;
      _ <- trigger (@IO _ unit "print" [r]↑);;
      cput v_lv (powder - 1)%Z;;;
      Ret r.

  Definition fnsems : fnsems_type :=
    [(Some CannonHdr.fire, (false, wmask_all, scopes, (None, cfunU fire)))].
  
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_lv, 1%Z↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End CannonI. End CannonI.
