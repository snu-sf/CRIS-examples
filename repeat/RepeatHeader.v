Require Import CRIS.
Require Export ImpPrelude.

Module RepeatName.
  Definition mn := "Repeat".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition repeat := fn "repeat".
End RepeatName.