From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Export ImpPrelude Imp.
From CRIS.imp_system.mem Require Export MemA.

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
