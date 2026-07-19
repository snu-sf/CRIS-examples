From CRIS.common Require Import CRIS.
Require Export ImpPrelude.

Module RepeatHdr.
  Definition mn := "Repeat".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition repeat := fnsig (fn "repeat") imp_fun_t.
End RepeatHdr.
