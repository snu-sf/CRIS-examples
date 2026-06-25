Require Import CRIS.

Module CtxHdr.

  Definition mn := "Ctx".
  
  Definition foo := fnsig "foo" (fntyp () ()).
  Definition cb_t := fntyp () Z.
  
End CtxHdr.
