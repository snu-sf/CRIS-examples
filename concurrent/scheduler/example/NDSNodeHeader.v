Require Import Common.

Module NDSNodeHdr.
  Definition f_main := fnsig "NDSNode.f_main" (fntyp SAny.t SAny.t).
  Definition f := fnsig "NDSNode.f" (fntyp SAny.t SAny.t).
End NDSNodeHdr.

Definition NDSNODE : string := "nds_node".
Global Opaque NDSNODE.
