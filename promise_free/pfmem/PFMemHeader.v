Require Import CRIS.
Require Export Basic Loc Val Ordering Event Local Configuration PFConfiguration.
Require Export View TView.

Module PFMemHdr.
  Definition alloc := "PFMem.alloc".
  Definition free  := "PFMem.free".
  Definition read  := "PFMem.read".
  Definition write := "PFMem.write".
  Definition cmp   := "PFMem.cmp".
  Definition cas   := "PFMem.cas".
  Definition faa   := "PFMem.faa".
  Definition fence := "PFMem.fence".
  Definition init  := "PFMem.init".
  Definition spawn := "PFMem.spawn".
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