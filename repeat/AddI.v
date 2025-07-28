Require Import CRIS.
Require Import Imp ImpPrelude.
Require Import AddHeader.
Require Import RepeatHeader.

Set Implicit Arguments.

Module AddI. Section AddI.
  Context `{Σ : GRA}.

  Definition scopes := [AddHdr.mn].

  Definition succ : list val → itree crisE val :=
    λ varg,
      'm : Z <- (pargs [Tint] varg)?;;
      Ret (Vint (m + 1)).

  Definition add (cenv: CEnv.t): list val → itree crisE val :=
    λ varg,
      '(n, m): _ <- ((pargs [Tint; Tint] varg)?);;
      fb <- ((cenv.(CEnv.id2blk) AddHdr.succ)?);;
      ccallU RepeatHdr.repeat [Vptr (fb, 0%Z); Vint n; Vint m].

  Definition fnsems (genv: GEnv.t) : fnsems_type:=
    [(Some AddHdr.succ, (false, wmask_all, scopes, (None, cfunU succ)));
     (Some AddHdr.add, (false, wmask_all, scopes, (None, cfunU (add (CEnv.load_genv genv)))))].

  Program Definition smod (genv: GEnv.t) : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t (genv: GEnv.t) : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none (smod genv)).
End AddI. End AddI.
