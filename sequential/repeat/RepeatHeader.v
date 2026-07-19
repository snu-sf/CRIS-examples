From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Export ImpPrelude.

Module RepeatHdr.
  Definition mn := "Repeat".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition repeat := fnsig (fn "repeat") imp_fun_t.
End RepeatHdr.
