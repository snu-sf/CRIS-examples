Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader.

Set Implicit Arguments.

Module MainI. Section MainI.
  Local Open Scope string_scope.

  Context `{Σ : GRA}.

  Variable num_fire: nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree hmodE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      'r : Z <- ccallU CannonHdr.fire ([] : list val);;
      trigger (@IO _ void "print" [r]↑);;;
      main_repeat n'
    end.

  Definition main : list val → itree hmodE unit :=
    λ _, main_repeat num_fire.

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(None, (false, wmask_all, scopes, (None, cfunU main)))].
  
  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).
End MainI. End MainI.