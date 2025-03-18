Require Import CRIS.
Require Import Imp ImpPrelude.
Require Import AddHeader.
Require Import RepeatHeader.

Set Implicit Arguments.

Module AddI. Section AddI.
  Context `{Σ : GRA}.

  Definition scopes := [AddName.mn].

  Definition succ : list val → itree pmodE val :=
    λ varg,
      'm : Z <- (pargs [Tint] varg)?;;
      Ret (Vint (m + 1)).

  Definition add (cenv: CEnv.t): list val → itree pmodE val :=
    λ varg,
      '(n, m): _ <- ((pargs [Tint; Tint] varg)?);;
      fb <- ((cenv.(CEnv.id2blk) AddName.succ)?);;
      ccallU RepeatName.repeat [Vptr fb 0; Vint n; Vint m].

  Definition fnsems (genv: GEnv.t) :=
    [(AddName.succ, (scopes, cfunU succ));
     (AddName.add, (scopes, cfunU (add (CEnv.load_genv genv))))].

  Program Definition Mod (genv: GEnv.t) : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems genv;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t (genv: GEnv.t) : HMod.t := Seal.sealing CRIS (PMod.to_hmod (Mod genv)).
End AddI. End AddI.
