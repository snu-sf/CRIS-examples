Require Export CRIS.common.CRIS.
From CRIS.modules Require Export SMod Mod.
Require Import ImpPrelude.

Module NDSHdr.
  Definition init         := fnsig "NDS.init" (fntyp (SAny.t) ()).
  Definition _spawn       := fnsig "NDS._spawn" (fntyp (string * SAny.t) ()).
  Definition spawn        := fnsig "NDS.spawn" (fntyp (string * SAny.t) nat).
  Definition yield        := fnsig "NDS.yield" (fntyp () ()).
  Definition yield_global := fnsig "NDS.yield_global" (fntyp () ()).
  Definition join         := fnsig "NDS.join" (fntyp (nat) (option SAny.t)).
  Definition get_tid      := fnsig "NDS.get_tid" (fntyp () nat).
End NDSHdr.

Definition NDS : string := "NDS".
Global Opaque NDS.

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

Module NDS. Section NDS.
  Import Events.

  Context `{E : Type → Type, coreE -< E, callE -< E}.

  Definition spawn (fnarg : string * SAny.t) : itree E nat :=
    'tid : nat <- ccallU NDSHdr.spawn fnarg;; Ret tid.

  Definition yield : itree E unit :=
    Seal.sealing NDS
     (iterC ((λ (_: unit),
        b <- trigger (Choose (option bool));;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true => 
            ccallU NDSHdr.yield tt;;;
            Ret (inl tt: () + ())
        end)) tt).

  Definition yield_global : itree E unit :=
    Seal.sealing NDS
     (iterC ((λ (_: unit),
        b <- trigger (Choose (option bool));;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true => 
            ccallU NDSHdr.yield_global tt;;;
            Ret (inl tt: () + ())
        end)) tt).

  Definition terminate : itree E unit :=
    Seal.sealing NDS
      (iterC ((λ (_: unit),
        ccallU NDSHdr.yield tt;;;
        Ret (inl tt: () + ())
      )) tt).

  Definition join (tid : nat) : itree E SAny.t :=
    'ors: option SAny.t <- ccallU NDSHdr.join tid;;
    rs <- ors?;;
    Ret rs.
End NDS. End NDS.

Notation 𝒩𝒩 := (NDS.yield).
Notation 𝒩𝒴 := (NDS.yield_global).

Lemma yield_global_unfold `{E : Type → Type, coreE -< E, callE -< E} :
  @NDS.yield_global E _ _ =
  tau;; b <- trigger (Choose (option bool));;
  match b with
  | None => Ret tt
  | Some false => NDS.yield_global
  | Some true => ccallU NDSHdr.yield_global tt;;; NDS.yield_global
  end.
Proof using.
  rewrite {1}/NDS.yield_global; unseal NDS; rewrite unfold_iterC.
  repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
  { ired. f_equal. extensionalities x. rewrite /NDS.yield_global; unseal NDS; ss. }
  { ired. rewrite /NDS.yield_global; unseal NDS; ss. }
  { ired. done. }
Qed.

Lemma yield_unfold `{E : Type → Type, coreE -< E, callE -< E} :
  @NDS.yield E _ _ =
  tau;; b <- trigger (Choose (option bool));;
  match b with
  | None => Ret tt
  | Some false => NDS.yield
  | Some true => ccallU NDSHdr.yield tt;;; NDS.yield
  end.
Proof using.
  rewrite {1}/NDS.yield; unseal NDS; rewrite unfold_iterC.
  repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
  { ired. f_equal. extensionalities x. rewrite /NDS.yield; unseal NDS; ss. }
  { ired. rewrite /NDS.yield; unseal NDS; ss. }
  { ired. done. }
Qed.
