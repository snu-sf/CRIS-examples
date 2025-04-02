Require Import CRIS.
Require Import MutHeader MutMainHeader APCHeader APC.

Set Implicit Arguments.

Module MutMainA. Section MutMainA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition scopes := ["MutMain"].

  Definition main_body : Any.t → itree hmodE Any.t :=
    λ _, pure;;; trigger (Choose Any.t).

  Definition main_spec: fspec :=
    fspec_simple
      (fun (_: unit) =>
        ((λ varg, (⌜varg = tt↑⌝)%I),
         (λ vret, (⌜vret = (Vint 55)↑⌝)%I))).

  Definition Sp: alist string fspec :=
    Seal.sealing CRIS [(MutMainHdr.main, main_spec)].

  Definition fnsems :=
    [(MutMainHdr.main, (scopes, mk_specbody main_spec main_body))].

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
