Require Import CRIS.
Require Import Imp.
Require Import RepeatHeader.

Set Implicit Arguments.

Module RepeatI. Section RepeatI.
  Context `{Σ : GRA}.

  Definition scopes := [RepeatHdr.mn].

  Definition repeat (cenv: CEnv.t): list val → itree crisE val :=
    λ varg, 
      '(fb, (n, x)) : _ <- (pargs [Tblk; Tint; Tint] varg)?;;
      assume(intrange_64 n);;;
      if (Z_lt_le_dec n 1)
      then Ret (Vint x)
      else
        fn <- (cenv.(CEnv.blk2id) fb)?;;
        v <- ccallU fn [Vint x];;
        ccallU RepeatHdr.repeat [Vptr (fb, 0%Z); Vint (n - 1); v].

  Definition fnsems (genv: GEnv.t) : fnsems_type :=
    [(Some RepeatHdr.repeat, (false, wmask_all, scopes, (None, cfunU (repeat (CEnv.load_genv genv: CEnv.t)))))].

  Program Definition smod (genv: GEnv.t) : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t (genv: GEnv.t) : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none (smod genv)).
End RepeatI. End RepeatI.
