From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.cannon Require Import CannonHeader CannonMainI CannonA CannonHeader.

Module MainA. Section MainA.
  Import CannonA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Variable num_fire : nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree crisE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      'r : Z <- ccallU CannonHdr.fire ([] : list val);;
      _ <- trigger (@IO _ unit "print" [r]↑);;
      main_repeat n'
    end.

  Definition main : Any.t → itree crisE Any.t :=
    λ _, main_repeat num_fire;;; Ret ()↑.

  Definition main_spec : fspec := fspec_simple (λ _ : unit, ((λ _, Ball), (λ _, True%I))).

  Definition fnsems : fnsemmap :=
    {[entry # (msk_scp scopes msk_true, (fsp_some main_spec, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End MainA. End MainA.
