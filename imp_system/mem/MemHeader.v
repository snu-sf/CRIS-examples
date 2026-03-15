Require Import CRIS.
Require Export ImpPrelude.

Module MemHdr.
  Definition alloc := "MemAtom.alloc".
  Definition free  := "MemAtom.free".
  Definition load  := "MemAtom.load".
  Definition store := "MemAtom.store".
  Definition cmp   := "MemAtom.cmp".
  Definition cas := "MemAtom.cas".

  Definition exports : gset string :=
    {[alloc; free; load; store; cmp; cas]}.

  Definition faa {E : Type → Type} `{callE -< E, coreE -< E} : list val → itree E val :=
    λ l,
    'v_raw : val <- ccallU MemHdr.load l;;
    'v : Z <- (pargs [Tint] [v_raw])?;;
    'r : val <- ccallU MemHdr.store (l ++ [Vint (v + 1)%Z]);;
    Ret v_raw.
End MemHdr.

Module memGSEnv.
  Definition t: GEnv.t :=
    [(MemHdr.alloc, Gfun↑);
     (MemHdr.free,  Gfun↑);
     (MemHdr.load, Gfun↑);
     (MemHdr.store, Gfun↑);
     (MemHdr.cmp, Gfun↑);
     (MemHdr.cas, Gfun↑)].
End memGSEnv.
