Require Import CRIS.common.Common.
From CRIS.imp_system Require Import imp.ImpPrelude.

Module IncrHdr.
  Definition incr := fnsig "incr" imp_fun_t.
End IncrHdr.

Module ClientHdr.
  Definition thread := fnsig "thread" imp_fun_t.
End ClientHdr.
