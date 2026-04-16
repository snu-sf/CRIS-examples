Require Import Common ImpPrelude.

Module SpinLockHdr.
  Definition newlock := fnsig "newlock" imp_fun_t.
  Definition acquire := fnsig "acquire" imp_fun_t.
  Definition release := fnsig "release" imp_fun_t.
End SpinLockHdr.

Module SpinLockMainHdr.
  Definition incr := fnsig "incr" imp_fun_t.
End SpinLockMainHdr.
