Require Import CRIS.

Module CellioHdr.
  Definition mn := "Cellio".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition set := fn "set".
  Definition get := fn "get".
End CellioHdr.

