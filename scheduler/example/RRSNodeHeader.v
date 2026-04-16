Require Import Common.

Module RRSNodeHdr.
  Definition f_main := fnsig "RRSNode.f_main" (fntyp SAny.t SAny.t).
  Definition f := fnsig "RRSNode.f" (fntyp SAny.t SAny.t).
End RRSNodeHdr.

Definition RRSNODE : string := "rrs_node".
Global Opaque RRSNODE.
