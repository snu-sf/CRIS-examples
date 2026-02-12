Require Export Common.
Require Export SMod.
Require Import ImpPrelude.
Require Export PFMemHeader.
Require Export Basic Val.

Module SystemHdr.
  Definition _spawn := "System._spawn".
  Definition spawn := "System.spawn".
  Definition yield := "System.yield".
  Definition get_tid := "System.get_tid".
  Definition alloc := "System.alloc".
  Definition write := "System.write".
  Definition read := "System.read".
End SystemHdr.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition sfunN {X Y} `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : X -> itree E Y) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓!;; vret <- body varg;; Ret vret↑↑.

  Definition sfunU {X Y} `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : X -> itree E Y) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓?;; vret <- body varg;; Ret vret↑↑.

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
            trigger (Call SystemHdr.yield tt↑);;;
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
      ccallU PFMemHdr.alloc (tid, sz).

  Definition write : Loc.t * Val.t * Ordering.t → itree E Val.t :=
    λ '(loc, val, ord),
      'tid : Ident.t <- ccallU SystemHdr.get_tid ();;
      ccallU PFMemHdr.write (tid, loc, val, ord).

  Definition read : Loc.t * Ordering.t → itree E Val.t :=
    λ '(loc, ord),
      'tid : Ident.t <- ccallU SystemHdr.get_tid ();;
      ccallU PFMemHdr.read (tid, loc, ord).
End System. End System.

Notation 𝒴 := (System.yield).