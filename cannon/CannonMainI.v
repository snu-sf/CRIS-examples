Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader.

Set Implicit Arguments.

Module MainI. Section MainI.
  Local Open Scope string_scope.

  Context `{Σ : GRA}.

  Variable num_fire: nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree pmodE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      'r : Z <- ccallU CannonName.fire ([] : list val);;
      trigger (@IO _ void "print" [r]↑);;;
      main_repeat n'
    end.

  Definition main : list val → itree pmodE unit :=
    λ _, main_repeat num_fire.

  Definition fnsems :=
    [(MainName.main, (scopes, cfunU main))].
  
  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (PMod.to_hmod Mod).
End MainI. End MainI.