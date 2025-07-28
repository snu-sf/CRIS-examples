Require Import CRIS.
Require Import MutHeader APCHeader APC.

Set Implicit Arguments.

Module MutFA. Section MutFA.
  Import MutAUX.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["MutF"].

  Definition f_spec: fspec :=
    fspec_apc (λ n: nat, n)%ord
      (fun (n: nat) =>
        ((λ varg, (⌜varg = [Vint (Z.of_nat n)]↑ ∧ n < mut_max⌝)%I),
         (λ vret, (⌜vret = (Vint (Z.of_nat (sum n)))↑⌝)%I))).
         
  Definition SpF: spl_type :=
    Seal.sealing CRIS [(Some MutHdr.mutf, Some f_spec)].

  Definition fnsems : fnsems_type :=
    [(Some MutHdr.mutf, (true, wmask_all, scopes, (Some f_spec, pure_body)))].

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := Seal.sealing CRIS (SMod.to_mod Sp smod).
End MutFA. End MutFA.
