Require Import Common ImpPrelude.

Module PQueueHdr.
  Definition new := fnsig "PQueue.new" imp_fun_t.
  Definition add := fnsig "PQueue.add" imp_fun_t.
  Definition remove_min := fnsig "PQueue.remove_min" imp_fun_t.
End PQueueHdr.