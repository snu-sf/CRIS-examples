From CRIS.common Require Import CRIS.
Require Export ImpPrelude Imp MemA.

Module KnotMainHdr.
Definition fib := fnsig "KnotMain.fib" imp_fun_t.
End KnotMainHdr.

Module KnotMainGEnv.
Definition t : GEnv.t :=
  [(KnotMainHdr.fib.1, Gfun↑)].
End KnotMainGEnv.
