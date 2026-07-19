From CRIS.common Require Import Common.

Module SingleCoinHdr.
  Definition new := fnsig "SingleCoin.new" (fntyp () nat).
  Definition read := fnsig "SingleCoin.read" (fntyp nat bool).
End SingleCoinHdr.