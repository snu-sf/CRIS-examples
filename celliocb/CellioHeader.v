Require Import CRIS.

Module CellioHdr.
  Definition mn := "Cellio".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition set := fn "set".
  Definition set_t := cftyp string ().

  Definition get := fn "get".
  Definition get_t := cftyp () Z.
End CellioHdr.

