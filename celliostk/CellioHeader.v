Require Import CRIS.

Module CellioHdr.
  Definition mn := "Cellio".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition new := fn "new".
  Definition push := fn "push".
  Definition pop := fn "pop".
End CellioHdr.

