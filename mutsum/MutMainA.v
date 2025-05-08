Require Import CRIS.
Require Import MutHeader MutMainHeader APCHeader APC.

Set Implicit Arguments.

Module MutMainA. Section MutMainA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Variable with_pure: bool.
  
  Definition scopes := ["MutMain"].

  Definition main_body : Any.t → itree hmodE Any.t :=
    λ _, (if with_pure then pure else Ret ()↑);;; Ret (Vint 55)↑.

  Definition main_spec: fspec :=
    fspec_simple
      (fun (_: unit) =>
        ((λ varg, (⌜varg = tt↑⌝)%I),
          (λ vret, (⌜True⌝)%I))).

  Definition Sp: alist string fspec :=
    Seal.sealing CRIS [(MutMainHdr.main, main_spec)].

  Definition fnsems :=
    [(MutMainHdr.main, (wmask_all, scopes, mk_specbody main_spec main_body))].

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
End MutMainA. End MutMainA.
