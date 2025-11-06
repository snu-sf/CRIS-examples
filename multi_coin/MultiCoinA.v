(* Require Import Coqlib Any Events.
Require Import Skeleton HMod SMod PCM IPM ITactics.
Require Import ProphecyA MultiCoinHeader MultiCoinASpec.
Require Import sWorld.
Require Import Streams.

Set Implicit Arguments.

Module MultiCoinA.
Section A.
  Local Open Scope list_scope.
  Context `{_W: CtxWD.t}.
  Context `{_A: MultiCoinAR.t (Γ:=Γ)}.
  Context `{_X: ProphecyAR.t (Γ := Γ)}.

  Definition scopes := ["MultiCoin"].
  Definition v_coins := "MultiCoin" ↯ "coins".
  
  Definition new: unit -> itree hmodE nat :=
    fun _ =>
      `cs : list (Stream bool) <- cgetU v_coins;;
      bs <- trigger (Choose (Stream bool));;
      cput v_coins (cs ++ [bs])%list;;;
      Ret (List.length cs)
  .

  Definition read: nat -> itree hmodE bool :=
    fun idx =>
      `cs : list (Stream bool) <- cgetU v_coins;;
      match nth_error cs idx with
      | Some bs => Ret (hd bs)
      | None => triggerNB
      end
  .

  Definition toss: nat -> itree hmodE unit :=
    fun idx =>
      `cs : list (Stream bool) <- cgetU v_coins;;
      match nth_error cs idx with
      | Some bs =>
          let new_cs := firstn idx cs ++ [tl bs] ++ skipn (S idx) cs in
          cput v_coins new_cs
      | _ => triggerUB
      end
  .

  Definition fnsems :=
    [(MultiCoinName.new, (scopes, mk_specbody MultiCoinAS.new_spec (cfunU new)));
     (MultiCoinName.read, (scopes, mk_specbody MultiCoinAS.read_spec (cfunU read)));
     (MultiCoinName.toss, (scopes, mk_specbody MultiCoinAS.toss_spec (cfunU toss)))].
  
  Program Definition Sem: SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [(v_coins, (@nil (Stream bool))↑)];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: SMod.t := {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := MultiCoinSK.t;
  |}
  .

  Definition InitCond : Sk.t -> iProp :=
    fun _ => (MultiCoinAS.free_from 0 ∗ MultiCoinAS.uninitialized_from 0)%I.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Definition t: HMod.t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End A.
End MultiCoinA. *)
