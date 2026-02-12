Require Import CRIS.
Require Export ImpPrelude.

Module MemHdr.
  Definition alloc := "MemH.alloc".
  Definition free  := "MemH.free".
  Definition load  := "MemH.load".
  Definition store := "MemH.store".
  Definition cmp   := "MemH.cmp".
  Definition cas   := "MemH.cas".
End MemHdr.
