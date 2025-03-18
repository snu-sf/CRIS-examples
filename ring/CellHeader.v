Require Import CRIS.

(* Function names as string *)
Module CellName.
  Definition mn (idx : nat) := "Cell" +:+ HexString.of_nat idx.

  Definition fn (idx : nat) (method : string) :=
    mn idx +:+ "." +:+ method.

  Definition get idx := fn idx "get".
  Definition set idx := fn idx "set".
End CellName.
