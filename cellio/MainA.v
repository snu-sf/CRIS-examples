Require Import CRIS.
Require Import CellioA CtxHeader CellioHeader.

Set Implicit Arguments.

Module MainAS. Section MainAS.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellioG}.

  Definition main_spec : fspec :=
    fspec_simple (fun _ : unit =>
                    ( fun arg => cell 0
                    , fun ret => True))%I.

End MainAS. End MainAS.

Module MainA. Section MainA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _CELLIO: !cellioG}.
                
  Definition scopes : list string := [].

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      'i: Z <- ccallU CtxHdr.input tt;;
      '_: unit <- ccallU CtxHdr.foo tt;;
      '_: unit <- trigger (IO "Print" i);;
      Ret tt↑.
  
  Definition fnsems : fnsemmap :=
    {[None := Some (msk_scp scopes msk_true, (fsp_some MainAS.main_spec, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.

End MainA. End MainA.
