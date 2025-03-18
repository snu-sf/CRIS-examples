Require Import CRIS.

Module CellioName.
  Definition mn := "Cellio".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition set := fn "set".
  Definition get := fn "get".
End CellioName.

