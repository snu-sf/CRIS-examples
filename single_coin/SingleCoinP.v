Require Import CRIS.
Require Import SingleCoinHeader ProphecyHeader.
(* From stdpp Require Import strings. *)

Module SingleCoinP. Section SingleCoinP.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.
  Context (mn : string).

  Definition scopes := ["SingleCoin"].

  Definition v_coins := "SingleCoin" ↯ "coins".
  Definition proph_coins (n : nat) : Prophecy.ID := ("SingleCoin", n↑↑).

  Definition new : unit → itree crisE nat :=
    λ _,
      'cs : list (option bool) <- cgetU v_coins;;
      cput v_coins (cs ++ [None])%list;;;
      ccallU (Y:=unit) (ProphecyName.new mn) (proph_coins (List.length cs));;;
      Ret (List.length cs).

  Definition read : nat → itree crisE bool :=
    λ idx,
      'cs : list (option bool) <- cgetU v_coins;;
      match cs !! idx with
      | Some (Some b) => Ret b
      | Some None =>
          b <- trigger (Choose bool);;
          cput v_coins ((firstn idx cs) ++ [Some b] ++ (skipn (S idx) cs))%list;;;
          ccallU (Y:=unit) (ProphecyName.resolve mn) (proph_coins idx, b↑↑);;;
          Ret b
      | None => triggerUB
      end.

  Definition fnsems : fnsemmap :=
    {[Some SingleCoinHdr.new := Some (msk_real (msk_scp scopes msk_true), (None, cfunU new));
      Some SingleCoinHdr.read := Some (msk_real (msk_scp scopes msk_true), (None, cfunU read))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_coins := Some (@nil (option bool))↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End SingleCoinP. End SingleCoinP.
