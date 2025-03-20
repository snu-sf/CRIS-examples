Require Import CRIS.
Require Export ImpPrelude Imp MemA.

Module KnotMainHdr.
Definition fib := "KnotMain.fib".
Definition main := "CRIS_init".
End KnotMainHdr.

Module KnotMainGEnv.
Definition t : GEnv.t :=
  [(KnotMainHdr.fib, Gfun↑);
   (KnotMainHdr.main, Gfun↑)].
End KnotMainGEnv.