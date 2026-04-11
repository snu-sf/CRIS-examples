Require Import CRIS.
Require Import ImpPrelude.

Module CellioHdr.
  Definition mn := "Cellio".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition new := fn "new".
  Definition new_t := cftyp () val.

  Definition push := fn "push".
  Definition push_t := cftyp (string * val) val.

  Definition pop := fn "pop".
  Definition pop_t := cftyp val (option Z * val).
End CellioHdr.

