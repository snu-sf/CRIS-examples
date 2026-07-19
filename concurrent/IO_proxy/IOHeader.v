Require Import CRIS.common.Common.
From CRIS.imp_system Require Import imp.ImpPrelude.

Module IOHdr.
  Definition init := fnsig "init" imp_fun_t.
  Definition request := fnsig "request" imp_fun_t.
  Definition proxy := fnsig "proxy" imp_fun_t.
End IOHdr.