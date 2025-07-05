Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonMainI CannonA CannonHeader.

Set Implicit Arguments.

Module MainAS. Section MainAS.
  Import CannonAS.
  Context `{!crisG Γ Σ α β τ _I _S}.

  Definition Sp : spl_type :=
    Seal.sealing CRIS [(None, None)].
End MainAS. End MainAS.

Module MainA. Section MainA.
  Import CannonAS.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{!cannonG}.

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

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(None, (true, wmask_all, scopes, (None, cfunU main)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := Ball.

  Definition t Sp := Seal.sealing CRIS (SMod.to_hmod Sp Mod).
End MainA. End MainA.
