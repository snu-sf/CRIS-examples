Require Import CRIS.
Require Import CellioHeader CtxHeader.

Set Implicit Arguments.

Module MainI. Section MainI.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.

  Definition scopes : list string := [].

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      ccallU (Y:=unit) CellioHdr.set tt;;;
      ccallU (Y:=unit) CtxHdr.foo tt;;;
      x <- ccallU (Y:=Z) CellioHdr.get tt;;
      trigger (@IO _ unit "Print" x);;;
      Ret tt↑.
  
  Definition fnsems : fnsemmap :=
    {[None := Some (msk_real (msk_scp scopes msk_true), (fsp_none, main))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.
  
  Definition t := SMod.to_mod ∅ smod.
End MainI. End MainI.
