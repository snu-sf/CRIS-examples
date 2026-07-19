From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Export ImpPrelude Imp.
From CRIS.imp_system.mem Require Export MemA.

Module KnotMainHdr.
Definition fib := fnsig "KnotMain.fib" imp_fun_t.
End KnotMainHdr.

Module KnotMainGEnv.
Definition t : GEnv.t :=
  [(KnotMainHdr.fib.1, Gfun↑)].
End KnotMainGEnv.
