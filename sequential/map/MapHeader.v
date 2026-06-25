Require Import CRIS.
Require Export ImpPrelude.

Module MapHdr.
  Definition init := fnsig "Map.init" imp_fun_t.
  Definition get  := fnsig "Map.get" imp_fun_t.
  Definition set  := fnsig "Map.set" imp_fun_t.
  Definition set_by_user := fnsig "Map.set_by_user" imp_fun_t.
End MapHdr.
