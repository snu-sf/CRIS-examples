Require Import CRIS.common.CRIS.

From Stdlib Require Import Orders MSetList FMapList OrderedTypeEx FunInd.

Require Import DataStructure.
Require Import Basic.

Set Implicit Arguments.

Module Tid := Ident.
Module Bid := PeanoNat.Nat.

Notation ofs := Z (only parsing).

Module TBid <: UsualDecidableType.
  Definition t : Set := (option Tid.t) * Bid.t.

  Definition eq_dec: forall (x y: t), {x = y} + {x <> y}.
  Proof. repeat (decide equality). Qed.

  Definition eq := @eq t.

  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Definition eqb: t -> t -> bool :=
    fun x y => andb (option_rel_bool Tid.eqb (fst x) (fst y)) (Nat.eqb (snd x) (snd y)).

  Lemma eqb_eq x y:
    eqb x y = true <-> x = y.
  Proof.
    destruct x, y. unfold eqb. ss. split; i; ss.
    - eapply andb_prop in H. des. eapply Nat.eqb_eq in H0.
      destruct o; inv H; des_ifs. eapply Tid.eqb_eq in H2. subst. eauto.
    - inv H. rewrite Nat.eqb_refl. destruct o0; ss. rewrite Tid.eqb_refl. ss.
  Qed.

  Lemma eqb_refl x:
    eqb x x = true.
  Proof.
    unfold eqb. destruct x; destruct o; ss; (try rewrite !Tid.eqb_refl); rewrite !Nat.eqb_refl; ss.
  Qed.
End TBid.

Module Loc <: UsualDecidableType.
  Structure _t: Type :=
    mk {
        tid: option Tid.t;
        bid: Bid.t;
        ofs: Z;
      }.

  Definition t := _t.

  Definition eq := @eq t.

  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Lemma eq_leibniz (x y: t): eq x y -> x = y.
  Proof. auto. Qed.

  Definition eq_dec : forall (x y : t), {x = y} + {x <> y}.
  Proof. repeat (decide equality). Qed.

  Definition eqb (x y : t) : bool :=
    option_rel_bool Tid.eqb (tid x) (tid y) &&
    Bid.eqb (bid x) (bid y) &&
    Z.eqb (ofs x) (ofs y).
  
  Lemma eqb_refl (x : t): eqb x x = true.
  Proof.
    unfold eqb.
    destruct x. ss.
    rewrite Nat.eqb_refl BinInt.Z.eqb_refl.
    destruct tid0; ss.
    rewrite Tid.eqb_refl. ss.
  Qed.

  Lemma eqb_eq (x y: t): eqb x y = true -> x = y.
  Proof.
    unfold eqb.
    destruct x, y. destruct tid0, tid1; ss.
    - i. repeat (apply andb_prop in H; des).
      rewrite Tid.eqb_eq in H; rewrite Bid.eqb_eq in H1; rewrite BinInt.Z.eqb_eq in H0. subst. ss.
    - i. eapply andb_prop in H. des.
      rewrite Nat.eqb_eq in H. rewrite BinInt.Z.eqb_eq in H0. subst. ss.
  Qed.

  Lemma eq_dec_eq A i (a1 a2 : A):
    (if eq_dec i i then a1 else a2) = a1.
  Proof.
    destruct (eq_dec i i); [|congruence]. auto.
  Qed.

  Lemma eq_dec_neq A i1 i2 (a1 a2:A)
        (NEQ: i1 <> i2):
    (if eq_dec i1 i2 then a1 else a2) = a2.
  Proof.
    destruct (eq_dec i1 i2); [congruence|]. auto.
  Qed.

  Definition id_eq_dec := pair_eq_dec (option_eq_dec Tid.eq_dec) Nat.eq_dec.

  Definition get_tbid l := (tid l, bid l).
End Loc.

Module LocFun := UsualFun (Loc).
