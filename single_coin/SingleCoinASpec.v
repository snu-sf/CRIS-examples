(* Require Import Coqlib Any Events.
Require Import HMod SMod.
Require Import PCM IPM STB sWorld ITactics. 
Require Import SingleCoinHeader.
Require Import ProphecyHeader ProphecyA.
From stdpp Require Import coPset gmap namespaces.
Require Import Ensembles.
Set Implicit Arguments.

Module SingleCoinPrT.

  Inductive Resolve (rs : bool) (P : Ensemble bool) : Ensemble bool :=
  | Restriction (IN: P rs) : Resolve rs P rs
  | Dummy b (NIN: not (P rs)) (ORI: P b) : Resolve rs P b
  .

  Program Definition t : ProphecyT.t :=
    {|
      ProphecyT.Pro := bool;
      ProphecyT.Obs := bool;
      ProphecyT.wf := fun _ P => Inhabited _ P;
      ProphecyT.resolve := fun _ => Resolve;
      ProphecyT.obs_default := true;
    |}.
  Next Obligation. econs. instantiate (1:=true). ss. Qed.
  Next Obligation.
    intros. inv WF. split.
    - destruct (classic (P obs)).
      + econs. instantiate (1 := obs). econs. et.
      + econs. instantiate (1 := x). econs; et.
    - ii. inv H0; et.
  Qed.
  Next Obligation.
    intros. exists (obs_seq 0). i. induction i; ss.
    destruct i. { ss. econs. et. }
    destruct (classic (obs_seq 0 = obs_seq (S i))).
    - rewrite H. econs. rewrite <- H. et.
    - econs; et. ii. apply H. clear H.
      revert H0 IHi. generalize (obs_seq 0) (obs_seq (S i)).
      induction i; ss.
      + i. inv IHi; ss; inv H0; ss. exfalso. apply NIN. ss.
      + i. inv IHi0; inv H0; et.
  Qed.

End SingleCoinPrT.

Module SingleCoinAS.
Section COIN.
  Context `{_W: CtxWD.t}.
  Context `{_X: ProphecyAR.t (Γ := Γ)}.

  Global Instance RA: URA.t := (nat ==> OneShot.t unit)%ra.
  Context `{@GRA.inG RA Γ}.

  Definition readable_r idx : RA :=
    fun _idx => if dec idx _idx then OneShot.white tt
                else ε.
  Definition readable idx : iProp := OwnM (readable_r idx).

  Definition uninitialized_r idx : RA :=
    fun _idx => if dec idx _idx then OneShot.black
                else ε.

  Definition uninitialized idx : iProp := OwnM (uninitialized_r idx).

  Definition uninitialized_from_r lo : RA :=
    fun _idx => if le_dec lo _idx then OneShot.black
                else ε.

  Definition uninitialized_from lo : iProp := OwnM (uninitialized_from_r lo).

  Definition SingleCoinFree_r (lo : nat) : (ProphecyT.ID ==> (Excl.t ()))%ra :=
    fun '(mn, sany) =>
      if decide (mn = "SingleCoin")
      then match sany↓↓ with
           | Some idx =>
               if le_dec lo idx then Excl.just tt
               else ε
           | _ => ε
           end
      else ε.

  Definition free_from_r (lo : nat) : ProphecyAS.IdRA := Auth.white (SingleCoinFree_r lo).

  Definition free_from (lo : nat) : iProp := OwnM (free_from_r lo).

  Definition new_spec: fspec :=
    fspec_simple (fun '() =>
     ((fun varg => True)%I,
      (fun vret => ∃ l, readable l)%I)).

  Definition read_spec: fspec :=
    fspec_simple (fun l =>
     ((fun varg => ⌜varg = l↑⌝ ∗ readable l)%I,
      (fun vret => readable l)%I)).

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(SingleCoinName.new, new_spec);
                        (SingleCoinName.read, read_spec)].
  
  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End COIN.
End SingleCoinAS.

Module SingleCoinAR.
  Class t
    `{@GRA.inG SingleCoinAS.RA Γ}
    := SingleCoinARes: unit.

End SingleCoinAR. *)
