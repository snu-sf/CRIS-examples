Require Import CRIS.
Require Export ImpPrelude Imp MemA.

Module KnotHdr.
Definition knot := "Knot.knot".
Definition rec := "Knot.rec".
Definition _f := "Knot._f".
End KnotHdr.

Module KnotGEnv.
Definition t : GEnv.t :=
  [(KnotHdr.knot, Gfun↑);
   (KnotHdr.rec, Gfun↑);
   (KnotHdr._f, (Gvar 0)↑)].
End KnotGEnv.
