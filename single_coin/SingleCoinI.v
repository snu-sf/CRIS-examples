Require Import CRIS.
Require Import SingleCoinHeader.

Module SingleCoinI. Section SingleCoinI.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS}.

  Definition scopes := ["SingleCoin"].
  Definition v_coins := "SingleCoin" ↯ "coins".

  Definition new : unit → itree crisE nat :=
    λ _,
      'cs : list (option bool) <- cgetU v_coins;;
      cput v_coins (cs ++ [None])%list;;;
      Ret (List.length cs).

  Definition read : nat → itree crisE bool :=
    λ idx,
      'cs : list (option bool) <- cgetU v_coins;;
      match cs !! idx with
      | Some (Some b) => Ret b
      | Some None =>
          b <- trigger (Choose bool);;
          cput v_coins ((firstn idx cs) ++ [Some b] ++ (skipn (S idx) cs))%list;;;
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
End SingleCoinI. End SingleCoinI.
