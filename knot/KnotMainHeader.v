Require Import CRIS.
Require Export ImpPrelude Imp MemA.

Module KnotMainHdr.
Definition fib := "KnotMain.fib".
End KnotMainHdr.

Module KnotMainGEnv.
Definition t : GEnv.t :=
  [(KnotMainHdr.fib, Gfun↑)].
End KnotMainGEnv.