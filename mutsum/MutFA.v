Require Import CRIS.
Require Import MutHeader APCHeader APC.

Set Implicit Arguments.

Module MutFA. Section MutFA.
  Import MutAUX.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, _CONC: !concGS}.

  Definition scopes := ["MutF"].

  Definition f_spec: fspec :=
    fspec_apc (λ n: nat, n)%ord
      (fun (n: nat) =>
        ((λ varg, (⌜varg = [Vint (Z.of_nat n)]↑ ∧ n < mut_max⌝)%I),
         (λ vret, (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝)%I))).
         
  Definition SpF: specmap :=
    {[speckey_fn MutHdr.mutf := fspec_to_rel f_spec]}.

  Definition fnsems : fnsemmap :=
    {[Some MutHdr.mutf := Some (msk_scp scopes msk_true, (fsp_some f_spec, pure_body))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := SMod.to_mod Sp smod.
End MutFA. End MutFA.
