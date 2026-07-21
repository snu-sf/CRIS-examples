Require Export CRIS.common.CRIS.
Require Export CRIS.modules.SMod.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.promise_free.pfmem Require Export PFMemHeader.
From CRIS.promise_free.lib Require Export Basic Val.

Module SystemHdr.
  Definition _spawn  := fnsig "System._spawn" (fntyp (Ident.t * string * SAny.t) ()).
  Definition spawn   := fnsig "System.spawn" (fntyp (string * SAny.t) ()).
  Definition yield   := fnsig "System.yield" (fntyp () ()).
  Definition get_tid := fnsig "System.get_tid" (fntyp () Ident.t).
  Definition alloc   := fnsig "System.alloc" (fntyp nat Val.t).
  Definition write   := fnsig "System.write" (fntyp (Loc.t * Val.t * Ordering.t) Val.t).
  Definition read    := fnsig "System.read" (fntyp (Loc.t * Ordering.t) Val.t).
End SystemHdr.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition interp_cond (s : {n & GTerm.t n}) :=
    match s with
    | existT n p => ⟦ p ⟧
    end.
End FSpec.

Module System. Section System.
  Import Events.

  Context {E : Type → Type}.
  Context `{coreE -< E, callE -< E}.

  Definition yield : itree E unit :=
    Seal.sealing "System"
      (iterC ((λ (_: unit),
        b <- trigger (Choose (option bool));;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true => 
            trigger (Call SystemHdr.yield.1 tt↑);;;
            Ret (inl tt: () + ())
        end)) tt).

  Definition terminate : itree E unit :=
    Seal.sealing "System"
      (iterC ((λ _,
        '() : _ <- ccallU SystemHdr.yield tt;;
        Ret (inl tt: () + ())
      )) tt).

  Definition alloc : nat → itree E Val.t :=
    λ sz,
      'tid : Ident.t <- ccallU SystemHdr.get_tid ();;
      ccallU (PFMemHdr.alloc) (tid, sz : Z).

  Definition write : Loc.t * Val.t * Ordering.t → itree E Val.t :=
    λ '(loc, val, ord),
      'tid : Ident.t <- ccallU SystemHdr.get_tid ();;
      ccallU (PFMemHdr.write) (tid, loc, val, ord).

  Definition read : Loc.t * Ordering.t → itree E Val.t :=
    λ '(loc, ord),
      'tid : Ident.t <- ccallU SystemHdr.get_tid ();;
      ccallU (PFMemHdr.read) (tid, loc, ord).
End System. End System.

Notation 𝒴 := (System.yield).
