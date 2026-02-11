Require Import CRIS.
Require Import ImpPrelude.
Require Import AddHeader.
Require Import APCHeader APC.

Set Implicit Arguments.

(* Define Specification *)
Module AddAS. Section AddAS.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (* mathematical succ *)
  Definition succ_fun n : Z :=
    (n + 1) : Z.

  (* mathematical add *)
  Definition add_fun n m : Z :=
    n + m %Z.

  Definition succ_spec : fspec :=
    fspec_apc (λ _, 0%ord)
      (λ n,
        (λ varg, ⌜varg = [Vint n]↑⌝%I,
          λ vret, ⌜vret = (Vint (succ_fun n))↑⌝%I)
      ).

  Definition add_spec : fspec :=
    fspec_apc (λ '(n, m), OrdArith.add Ord.omega (Z.to_nat (n + 1))%ord)
      (λ '(n, m),
        (λ varg, ⌜varg = [Vint n; Vint m]↑ ∧ intrange_64 n ∧ (0 ≤ n)%Z⌝%I,
          λ vret, ⌜vret = (Vint (add_fun n m))↑⌝%I)
      ).

  Definition Sp : spl_type :=
    Seal.sealing CRIS
      [(Some AddHdr.succ, fsp_some succ_spec); (Some AddHdr.add, fsp_some add_spec)].
  
  Lemma Sp_nodup: List.NoDup (List.map fst Sp).
  Proof. unfold Sp. unseal CRIS. prove_nodup. Qed.

End AddAS. End AddAS.

(* Define Module *)
Module AddA. Section AddA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [AddHdr.mn].

  Definition fnsems : fnsems_type :=
    [(Some AddHdr.succ, (true, wmask_all, scopes, (fsp_some AddAS.succ_spec, pure_body)));
     (Some AddHdr.add, (true,wmask_all, scopes, (fsp_some AddAS.add_spec, pure_body)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp smod).
End AddA. End AddA.
