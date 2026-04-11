Require Import CRIS ImpPrelude.
Require Import CannonHeader.

Module MainI. Section MainI.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Variable num_fire : nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree crisE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      r <- ccallU CannonHdr.fire_t CannonHdr.fire ([] : list val);;
      trigger (@IO _ void "print" [r]↑);;;
      main_repeat n'
    end.

  Definition main : list val → itree crisE unit :=
    λ _, main_repeat num_fire.

  Definition fnsems : fnsemmap :=
    {[entry # (msk_scp scopes msk_true, (None, cfunU (_,_) main))]}.
  
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End MainI. End MainI.
