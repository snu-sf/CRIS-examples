Require Import CRIS.
Require Import ImpPrelude.

Module CellioHdr.
  Definition mn := "Cellio".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition new := fnsig (fn "new") (fntyp () val).
  Definition push := fnsig (fn "push") (fntyp (string * val) val).
  Definition pop := fnsig (fn "pop") (fntyp val (option Z * val)).
End CellioHdr.

