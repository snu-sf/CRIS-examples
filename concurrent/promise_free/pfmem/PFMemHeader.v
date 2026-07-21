Require Import CRIS.common.CRIS.
From CRIS.promise_free.lib Require Export Basic Loc Val Ordering Event.
From CRIS.promise_free.model Require Export
  Local Configuration PFConfiguration View TView.

Module PFMemHdr.
  Definition alloc := fnsig "PFMem.alloc" (fntyp (Ident.t * Z) Val.t).
  Definition free  := fnsig "PFMem.free" (fntyp (Ident.t * Loc.t) Val.t).
  Definition read  := fnsig "PFMem.read" (fntyp (Ident.t * Loc.t * Ordering.t) Val.t).
  Definition write := fnsig "PFMem.write" (fntyp (Ident.t * Loc.t * Val.t * Ordering.t) Val.t).
  Definition cmp   := fnsig "PFMem.cmp" (fntyp (Ident.t * Val.t * Val.t) Val.t).
  Definition cas   := fnsig "PFMem.cas" (fntyp (Ident.t * Loc.t * Val.t * Val.t * Ordering.t * Ordering.t) Val.t).
  Definition faa   := fnsig "PFMem.faa" (fntyp (Ident.t * Loc.t * Val.t * Ordering.t * Ordering.t) Val.t).
  Definition fence := fnsig "PFMem.fence" (fntyp (Ident.t * Ordering.t * Ordering.t) Val.t).
  Definition spawn := fnsig "PFMem.spawn" (fntyp Ident.t Ident.t).
End PFMemHdr.

Definition parse_loc `{Σ : GRA} : Val.t → itree crisE Loc.t :=
  λ v,
    match v with
    | Val.Vptr loc => Ret loc
    | _ => triggerUB
    end.

Definition parse_num `{Σ : GRA} : Val.t → itree crisE Z :=
  λ v,
    match v with
    | Val.Vnum v => Ret v
    | _ => triggerUB
    end.
