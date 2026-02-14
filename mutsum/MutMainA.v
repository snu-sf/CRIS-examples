Require Import CRIS.
Require Import MutHeader APCHeader APC.

Set Implicit Arguments.

Module MutMainA. Section MutMainA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Variable with_pure: bool.
  
  Definition scopes := ["MutMain"].

  Definition main_body : Any.t → itree crisE Any.t :=
    λ _, (if with_pure then pure else Ret ()↑);;; Ret (Vint 55)↑.

  (* Definition Sp: specmap := *)
  (*   {[speckey_entry := fspec_to_rel fspec_trivial]}. *)

  Definition fnsems : fnsemmap :=
    {[None := Some (msk_scp scopes msk_true, (None, main_body))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := SMod.to_mod Sp smod.
End MutMainA. End MutMainA.
