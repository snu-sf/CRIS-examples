From CRIS.common Require Import CRIS.
Require Export ImpPrelude Imp MemA.

Module KnotHdr.
Definition knot := fnsig "Knot.knot" imp_fun_t.
Definition rec := fnsig "Knot.rec" imp_fun_t.
Definition _f := fnsig "Knot._f" imp_fun_t.
End KnotHdr.

Module KnotGEnv.
Definition t : GEnv.t :=
  [(KnotHdr.knot.1, Gfun↑);
   (KnotHdr.rec.1, Gfun↑);
   (KnotHdr._f.1, (Gvar 0)↑)].
End KnotGEnv.
