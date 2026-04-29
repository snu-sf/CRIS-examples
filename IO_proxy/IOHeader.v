Require Import Common ImpPrelude.

Module IOHdr.
  Definition init := fnsig "init" imp_fun_t.
  Definition request := fnsig "request" imp_fun_t.
  Definition proxy := fnsig "proxy" imp_fun_t.
End IOHdr.