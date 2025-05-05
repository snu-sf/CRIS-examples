Require Import CRIS.
Require Import Imp.
Require Import RepeatHeader.

Set Implicit Arguments.

Module RepeatI. Section RepeatI.
  Context `{Σ : GRA}.

  Definition scopes := [RepeatHdr.mn].

  Definition repeat (cenv: CEnv.t): list val → itree pmodE val :=
    λ varg, 
      '(fb, (n, x)) : _ <- (pargs [Tblk; Tint; Tint] varg)?;;
      assume(intrange_64 n);;;
      if (Z_lt_le_dec n 1)
      then Ret (Vint x)
      else
        fn <- (cenv.(CEnv.blk2id) fb)?;;
        v <- ccallU fn [Vint x];;
        ccallU RepeatHdr.repeat [Vptr (fb, 0%Z); Vint (n - 1); v].

  Definition fnsems (genv: GEnv.t) :=
    [(RepeatHdr.repeat, (wmask_all, scopes, cfunU (repeat (CEnv.load_genv genv: CEnv.t))))].

  Program Definition Mod (genv: GEnv.t) : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems genv;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t (genv: GEnv.t) : HMod.t := Seal.sealing CRIS (PMod.to_hmod (Mod genv)).
End RepeatI. End RepeatI.
