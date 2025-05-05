Require Import CRIS.
Require Import MutHeader APCHeader APC.

Set Implicit Arguments.

Module MutGA. Section MutGA.
  Import MutAUX.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Definition scopes := ["MutG"].

  Definition g_spec: fspec :=
    fspec_apc (λ n: nat, n)%ord
      (fun (n: nat) =>
        ((λ varg, (⌜varg = [Vint (Z.of_nat n)]↑ ∧ n < mut_max⌝)%I),
         (λ vret, (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝)%I))).
         
  Definition SpG: alist string fspec :=
    Seal.sealing CRIS [(MutHdr.mutg, g_spec)].

  Definition fnsems :=
    [(MutHdr.mutg, (wmask_all, scopes, mk_specbody g_spec pure_body))].

  Program Definition Mod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := Seal.sealing CRIS (SMod.to_hmod Sp Mod).
End MutGA. End MutGA.
