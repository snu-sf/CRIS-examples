Require Import Common ImpPrelude.

Module IncrHdr.
  Definition incr := fnsig "incr" imp_fun_t.
End IncrHdr.

Module ClientHdr.
  Definition thread := fnsig "thread" imp_fun_t.
End ClientHdr.
