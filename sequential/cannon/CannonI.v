From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.cannon Require Import CannonHeader.

Module CannonI. Section CannonI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv". (* local variable *)

  Definition div (n m : Z) : option Z :=
    if Z_zerop m then None else Some (Z.div n m).

  Definition fire : list val → itree crisE Z :=
    λ _,
      powder <- cgetU v_lv;;
      r <- (div 1 powder)?;;
      _ <- trigger (@IO _ unit "print" [r]↑);;
      cput v_lv (powder - 1)%Z;;;
      Ret r.

  Definition fnsems : fnsemmap :=
    {[fid CannonHdr.fire # (msk_scp scopes msk_true, (None, cfunU CannonHdr.fire fire))]}.
  
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_lv # 1%Z↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CannonI. End CannonI.
