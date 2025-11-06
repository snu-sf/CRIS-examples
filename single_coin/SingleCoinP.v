Require Import CRIS.
Require Import SingleCoinHeader ProphecyHeader.
From stdpp Require Import strings.

Module SingleCoinP. Section SingleCoinP.

  Context `{Σ: GRA}.

  Definition scopes := ["SingleCoin"].

  Definition v_coins := "SingleCoin" ↯ "coins".
  Definition proph_coins (n : nat) : Prophecy.ID := ("SingleCoin", n↑↑).

  Definition new : unit → itree crisE nat :=
    λ _,
      'cs : list (option bool) <- cgetU v_coins;;
      cput v_coins (cs ++ [None])%list;;;
      ccallU (Y:=unit) ProphecyName.new (proph_coins (List.length cs));;;
      Ret (List.length cs).

  Definition read : nat → itree crisE bool :=
    λ idx,
      'cs : list (option bool) <- cgetU v_coins;;
      match nth_error cs idx with
      | Some (Some b) => Ret b
      | Some None =>
          b <- trigger (Choose bool);;
          cput v_coins ((firstn idx cs) ++ [Some b] ++ (skipn (S idx) cs))%list;;;
          ccallU (Y:=unit) ProphecyName.resolve (proph_coins idx, b↑↑);;;
          Ret b
      | None => triggerUB
      end.

  Definition fnsems : fnsems_type :=
    [(Some SingleCoinHdr.new, (false, wmask_all, scopes, (None, cfunU new)));
     (Some SingleCoinHdr.read, (false, wmask_all, scopes, (None, cfunU read)))
    ].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_coins, (@nil (option bool))↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).
End SingleCoinP. End SingleCoinP.
