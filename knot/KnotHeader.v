Require Import CRIS.
Require Export ImpPrelude Imp MemA.

Module KnotName.
Definition knot := "Knot.knot".
Definition rec := "Knot.rec".
Definition _f := "Knot._f".
End KnotName.

Module KnotGEnv.
Definition t : GEnv.t :=
  [(KnotName.knot, Gfun↑);
   (KnotName.rec, Gfun↑);
   (KnotName._f, (Gvar 0)↑)].
End KnotGEnv.
