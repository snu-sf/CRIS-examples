From CRIS.common Require Import CRIS.
Require Import MutHeader.
From CRIS.apc Require Import APCHeader APC.

Set Implicit Arguments.

Module MutGA. Section MutGA.
  Import MutAUX.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Definition scopes := ["MutG"].

  Definition g_spec: fspec :=
    fspec_apc (λ n: nat, n)%ord
      (fun (n: nat) =>
        ((λ varg, (⌜varg = [Vint (Z.of_nat n)]↑ ∧ n < mut_max⌝)%I),
         (λ vret, (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝)%I))).
         
  Definition SpG: specmap :=
    {[fid MutHdr.mutg @ g_spec]}.

  Definition fnsems : fnsemmap :=
    {[fid MutHdr.mutg # (msk_scp scopes msk_true, (fsp_some g_spec, pure_body))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := SMod.to_mod Sp smod.
End MutGA. End MutGA.
