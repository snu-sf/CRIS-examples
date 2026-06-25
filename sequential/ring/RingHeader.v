Require Import CRIS.

(* Function names as string *)
Module RingHdr.
  Definition init     := fnsig "Ring.init" (fntyp () ()).
  Definition get_size := fnsig "Ring.get_size" (fntyp () nat).
  Definition enqueue  := fnsig "Ring.enqueue" (fntyp Z ()).
  Definition dequeue  := fnsig "Ring.dequeue" (fntyp () Z).
End RingHdr.
