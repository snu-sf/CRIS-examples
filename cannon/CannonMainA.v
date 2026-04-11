Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonMainI CannonA CannonHeader.

Module MainA. Section MainA.
  Import CannonA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Variable num_fire : nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree crisE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      'r : Z <- ccallU CannonHdr.fire_t CannonHdr.fire ([] : list val);;
      _ <- trigger (@IO _ void "print" [r]↑);;
      main_repeat n'
    end.

  Definition main : list val → itree crisE unit :=
    λ _, main_repeat num_fire.

  Definition main_spec : fspec := fspec_simple (λ _ : unit, ((λ _, Ball), (λ _, True%I))).

  Definition fnsems : fnsemmap :=
    {[entry # (msk_scp scopes msk_true, (fsp_some main_spec, cfunU (_,_) main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End MainA. End MainA.
