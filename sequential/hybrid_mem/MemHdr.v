From CRIS.common Require Import CRIS.
Require Export ImpPrelude.

Module MemHdr.
  Definition alloc := fnsig "MemH.alloc" imp_fun_t.
  Definition free  := fnsig "MemH.free" imp_fun_t.
  Definition load  := fnsig "MemH.load" imp_fun_t.
  Definition store := fnsig "MemH.store" imp_fun_t.
  Definition cmp   := fnsig "MemH.cmp" imp_fun_t.
  Definition cas   := fnsig "MemH.cas" imp_fun_t.
End MemHdr.
