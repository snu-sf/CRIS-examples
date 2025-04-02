Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonMainI CannonA CannonHeader.

Set Implicit Arguments.

Module MainAS. Section MainAS.
  Import CannonAS.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_cannonG: !cannonG}.

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ arg, ⌜arg = tt↑⌝ ∗ Ball),
      (λ ret, ⌜ret = tt↑⌝))
    )%I.

  Definition Sp : alist string fspec :=
    Seal.sealing CRIS [(MainHdr.main, main_spec)].
End MainAS. End MainAS.

Module MainA. Section MainA.
  Import CannonAS.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_cannonG: !cannonG}.

  Variable num_fire : nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree hmodE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      'r : Z <- ccallU CannonHdr.fire ([] : list val);;
      _ <- trigger (@IO _ void "print" [r]↑);;
      main_repeat n'
    end.

  Definition main : list val → itree hmodE unit :=
    λ _, main_repeat num_fire.

  Definition fnsems :=
    [(MainHdr.main, (scopes, mk_specbody MainAS.main_spec (cfunU main)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := True%I.

  Definition t Sp := Seal.sealing CRIS (SMod.to_hmod Sp Mod).
End MainA. End MainA.
