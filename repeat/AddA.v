Require Import CRIS.
Require Import ImpPrelude.
Require Import AddHeader.
Require Import APCHeader APC.

Set Implicit Arguments.

(* Define Specification *)
Module AddAS. Section AddAS.

  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

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

  Definition Spc : alist string fspec :=
    Seal.sealing CRIS
      [(AddName.succ, succ_spec); (AddName.add, add_spec)]. 
  
  Lemma Spc_nodup: List.NoDup (List.map fst Spc).
  Proof. unfold Spc. unseal CRIS. prove_nodup. Qed.

End AddAS. End AddAS.

(* Define Module *)
Module AddA. Section AddA.

  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition scopes := [AddName.mn].

  Definition fnsems :=
    [(AddName.succ, (scopes, mk_specbody AddAS.succ_spec pure_body));
     (AddName.add, (scopes, mk_specbody AddAS.add_spec pure_body))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t u spc := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) spc Mod).
End AddA. End AddA.
