From CRIS.common Require Import CRIS.

Module CellioHdr.
  Definition mn := "Cellio".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition set := fnsig (fn "set") (fntyp () ()).
  Definition get := fnsig (fn "get") (fntyp () Z).
End CellioHdr.

