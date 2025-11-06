(* Require Import Coqlib Any Events.
Require Import HMod SMod.
Require Import PCM IPM STB sWorld ITactics. 
Require Import MultiCoinHeader.
Require Import ProphecyHeader ProphecyA.
From stdpp Require Import coPset gmap namespaces.
Require Import Ensembles Streams.
Set Implicit Arguments.

Module MultiCoinPrT.

  Definition Resolve (rep : nat) (b : bool) (P : Ensemble (Stream bool)) : Ensemble (Stream bool) := fun bs => P bs /\ Str_nth rep bs = b.

  Fixpoint prelist_app {A} (bs_pre : list A) (bs_post : Stream A) : Stream A :=
    match bs_pre with
    | hd :: tl => Cons hd (prelist_app tl bs_post)
    | _ => bs_post
    end.

  CoFixpoint seq_trace {A} (seq: nat -> A) (from : nat) : Stream A :=
    Cons (seq from) (seq_trace seq (S from)).

  Lemma Str_nth_prelist_app {A} i (bs_pre : list A) bs_post b
    (FIND : nth_error bs_pre i = Some b) : Str_nth i (prelist_app bs_pre bs_post) = b.
  Proof.
    revert b i FIND. induction bs_pre; ii. { destruct i; clarify. }
    destruct i. { ss. clarify. }
    ss. unfold Str_nth. ss. apply IHbs_pre; et.
  Qed.

  Lemma app_prelist_app {A} (bs_pre : list A) bs_post b :
    prelist_app bs_pre (Cons b bs_post) = prelist_app (bs_pre ++ [b]) bs_post.
  Proof. revert b. induction bs_pre; ss. i. f_equal. et. Qed.

  Program Definition t : ProphecyT.t :=
    {|
      ProphecyT.Pro := Stream bool;
      ProphecyT.Obs := bool;
      ProphecyT.wf :=
        fun n P => exists bs_pre, List.length bs_pre = n /\ forall bs_post, P (prelist_app bs_pre bs_post);
      ProphecyT.resolve := Resolve;
      ProphecyT.obs_default := true;
    |}.
  Next Obligation. ss. exists []. ss. Qed.
  Next Obligation.
    ss. ii. split; cycle 1. { ii. inv H. et. }
    des. exists (bs_pre ++ [obs]). split. { rewrite app_length. ss. nia. }
    i. econs. { rewrite <- app_prelist_app. et. }
    apply Str_nth_prelist_app. rewrite nth_error_app2; try nia.
    replace (n - _) with 0 by nia. ss.
  Qed.
  Next Obligation.
    intros. exists (seq_trace obs_seq 0). i. induction i; ss.
    econs; et. clear IHi. set 0. set i at 2. replace n0 with (n + i) by ss.
    clear n0. clearbody n. revert n. induction i; ss.
    - i. rewrite plus_0_r. unfold Str_nth. ss.
    - i. unfold Str_nth in *. ss. rewrite IHi. f_equal. nia.
  Qed.

End MultiCoinPrT.

Module MultiCoinAS.
Section COIN.
  Context `{_W: CtxWD.t}.
  Context `{_X: ProphecyAR.t (Γ := Γ)}.

  Global Instance RA: URA.t := (nat ==> OneShot.t unit)%ra.
  Context `{@GRA.inG RA Γ}.

  Definition available_r idx : RA :=
    fun _idx => if dec idx _idx then OneShot.white tt
                else ε.
  Definition available idx : iProp := OwnM (available_r idx).

  Definition uninitialized_r idx : RA :=
    fun _idx => if dec idx _idx then OneShot.black
                else ε.

  Definition uninitialized idx : iProp := OwnM (uninitialized_r idx).

  Definition uninitialized_from_r lo : RA :=
    fun _idx => if le_dec lo _idx then OneShot.black
                else ε.

  Definition uninitialized_from lo : iProp := OwnM (uninitialized_from_r lo).

  Definition MultiCoinFree_r (lo : nat) : (ProphecyT.ID ==> (Excl.t ()))%ra :=
    fun '(mn, sany) =>
      if decide (mn = "MultiCoin")
      then match sany↓↓ with
           | Some idx =>
               if le_dec lo idx then Excl.just tt
               else ε
           | _ => ε
           end
      else ε.

  Definition free_from_r (lo : nat) : ProphecyAS.IdRA := Auth.white (MultiCoinFree_r lo).

  Definition free_from (lo : nat) : iProp := OwnM (free_from_r lo).

  Definition new_spec: fspec :=
    fspec_simple (fun '() =>
     ((fun varg => True)%I,
      (fun vret => ∃ l, available l)%I)).

  Definition read_spec: fspec :=
    fspec_simple (fun l =>
     ((fun varg => ⌜varg = l↑⌝ ∗ available l)%I,
      (fun vret => available l)%I)).

  Definition toss_spec: fspec :=
    fspec_simple (fun l =>
     ((fun varg => ⌜varg = l↑⌝ ∗ available l)%I,
      (fun vret => available l)%I)).

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(MultiCoinName.new, new_spec);
                        (MultiCoinName.read, read_spec);
                        (MultiCoinName.toss, toss_spec)].
  
  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End COIN.
End MultiCoinAS.

Module MultiCoinAR.
  Class t
    `{@GRA.inG MultiCoinAS.RA Γ}
    := MultiCoinARes: unit.

End MultiCoinAR. *)
