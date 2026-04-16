Require Import CRIS.
Require Export ImpPrelude.

Module MemHdr.
  Definition alloc := fnsig "MemAtom.alloc" imp_fun_t.
  Definition free  := fnsig "MemAtom.free" imp_fun_t.
  Definition load  := fnsig "MemAtom.load" imp_fun_t.
  Definition store := fnsig "MemAtom.store" imp_fun_t.
  Definition cmp   := fnsig "MemAtom.cmp" imp_fun_t.
  Definition cas   := fnsig "MemAtom.cas" imp_fun_t.

  Definition exports : gset string :=
    {[alloc.1; free.1; load.1; store.1; cmp.1; cas.1]}.

  Definition faa {E : Type → Type} `{callE -< E, coreE -< E} : list val → itree E val :=
    λ l,
    'v_raw : val <- ccallU MemHdr.load l;;
    'v : Z <- (pargs [Tint] [v_raw])?;;
    'r : val <- ccallU MemHdr.store (l ++ [Vint (v + 1)%Z]);;
    Ret v_raw.
End MemHdr.

Module memGSEnv.
  Definition t: GEnv.t :=
    [(MemHdr.alloc.1, Gfun↑);
     (MemHdr.free.1,  Gfun↑);
     (MemHdr.load.1, Gfun↑);
     (MemHdr.store.1, Gfun↑);
     (MemHdr.cmp.1, Gfun↑);
     (MemHdr.cas.1, Gfun↑)].
End memGSEnv.
