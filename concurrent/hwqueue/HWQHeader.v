Require Import CRIS.common.Common ImpPrelude.

Module HWQHdr.
  Definition new_queue := fnsig "new_queue" imp_fun_t.
  Definition enqueue := fnsig "enqueue" imp_fun_t.
  Definition dequeue := fnsig "dequeue" imp_fun_t.
End HWQHdr.
