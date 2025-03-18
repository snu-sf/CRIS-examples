Require Import CRIS.
Require Export ImpPrelude Imp MemA.

Module KnotMainName.
Definition fib := "KnotMain.fib".
Definition main := "CRIS_init".
End KnotMainName.

Module KnotMainGEnv.
Definition t : GEnv.t :=
  [(KnotMainName.fib, Gfun↑);
   (KnotMainName.main, Gfun↑)].
End KnotMainGEnv.