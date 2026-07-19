From CRIS.common Require Import CRIS.

(* Function names as string *)
Module CellHdr.
  Definition mn (idx : nat) := "Cell" +:+ HexString.of_nat idx.

  Definition fn (idx : nat) (method : string) :=
    mn idx +:+ "." +:+ method.

  Definition get idx := fnsig (fn idx "get") (fntyp () Z).
  Definition set idx := fnsig (fn idx "set") (fntyp Z ()).
End CellHdr.
