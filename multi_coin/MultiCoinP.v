(* Require Import Coqlib Any Events.
Require Import Skeleton HMod PMod ITactics.
Require Import ProphecyHeader MultiCoinHeader.

Require Import sWorld.

Set Implicit Arguments.

Module MultiCoinP.
Section P.
  Local Open Scope list_scope.
  Context `{_W: CtxWD.t}.

  Definition scopes := ["MultiCoin"].
  Definition v_coins := "MultiCoin" ↯ "coins".
  Definition proph_coins (n: nat) : ProphecyT.ID := ("MultiCoin", n↑↑).

  Definition new: unit -> itree pmodE nat :=
    fun optn =>
      `cs : list bool <- cgetU v_coins;;
      b <- trigger (Choose bool);;
      `_ : unit <- ccallU ProphecyName.new (proph_coins (List.length cs));;
      cput v_coins (cs ++ [b])%list;;;
      Ret (List.length cs)
  .

  Definition read: nat -> itree pmodE bool :=
    fun idx =>
      `cs : list bool <- cgetU v_coins;;
      match nth_error cs idx with
      | Some b => Ret b
      | None => triggerUB
      end
  .

  Definition toss: nat -> itree pmodE unit :=
    fun idx =>
      `cs : list bool <- cgetU v_coins;;
      match nth_error cs idx with
      | Some b =>
          b <- trigger (Choose bool);;
          `_ : unit <- ccallU ProphecyName.resolve (proph_coins idx, b);;
          let new_cs := firstn idx cs ++ [b] ++ skipn (S idx) cs in
          cput v_coins new_cs
      | _ => triggerUB
      end
  .

  Definition fnsems :=
    [(MultiCoinName.new, (scopes, cfunU new));
     (MultiCoinName.read, (scopes, cfunU read));
     (MultiCoinName.toss, (scopes, cfunU toss))].
  
  Program Definition Sem: PModSem.t := {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [(v_coins, (@nil bool)↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: PMod.t := {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := MultiCoinSK.t;
  |}
  .

  Definition t: HMod.t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End P.
End MultiCoinP. *)
