Require Import CRIS.

Module CelliocbHdr.
  Definition mn := "Celliocb".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition set := fn "set".
  Definition get := fn "get".
End CelliocbHdr.

