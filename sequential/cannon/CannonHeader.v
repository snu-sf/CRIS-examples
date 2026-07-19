From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.

Module CannonHdr.
  Definition fire := fnsig "Cannon.fire" (fntyp (list val) Z).
End CannonHdr.
