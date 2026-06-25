Require Import CRIS.

From Stdlib Require Import FMapFacts MSetList.
Require Import UsualFMapPositive.
Require Import DataStructure.

Set Implicit Arguments.

Module Ident <: OrderedTypeWithLeibniz.
  Include BinPos.Pos.

  Lemma eq_leibniz (x y: t): eq x y -> x = y.
  Proof. auto. Qed.

  Ltac ltb_tac :=
    match goal with
    | [H: compare ?x1 ?x2 = _ |- _] =>
      generalize (compare_spec x1 x2); rewrite H; clear H;
      intro H; inversion H; subst; clear H
    | [H: lt ?x ?x |- _] =>
      destruct lt_strorder; congruence
    | [H: lt ?x ?y |- _] =>
      rewrite H in *; clear H
    | [H: eq ?x ?y |- _] =>
      rewrite H in *; clear H
    end.

  Lemma eq_dec_eq A i (a1 a2:A):
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
End Ident.

Module IdentFun := UsualFun (Ident).
Module IdentSet := UsualSet (Ident).
Module IdentMap := UsualPositiveMap.

Notation rtc := (clos_refl_trans_1n _). (* reflexive transitive closure *)
Notation rc := (clos_refl _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
#[export]
Hint Immediate rt1n_refl rt1n_trans t_step: core.
#[export]
Hint Resolve Relation_Operators.rt1n_trans: core.

Global Program Instance rtc_PreOrder A (R:A -> A -> Prop): PreOrder (rtc R).
Next Obligation. intros ? ? ? ?. induction H; et. Qed.

Lemma rtc_tail A R
      (a1 a3:A)
      (REL: rtc R a1 a3):
  (exists a2, rtc R a1 a2 /\ R a2 a3) \/
  (a1 = a3).
Proof.
  induction REL; auto. des; subst.
  - left. eexists. splits; [|eauto].
    econs; eauto.
  - left. eexists. splits; eauto.
Qed.

Lemma rtc_implies A (R1 R2: A -> A -> Prop)
      (IMPL: forall a b, R1 a b -> R2 a b):
  forall a b, rtc R1 a b -> rtc R2 a b.
Proof.
  i. induction H; eauto.
Qed.

Lemma rtc_refl
      A R (a b:A)
      (EQ: a = b):
  rtc R a b.
Proof. subst. econs. Qed.

Lemma rtc_n1
      A R (a b c:A)
      (AB: rtc R a b)
      (BC: R b c):
  rtc R a c.
Proof.
  etrans; eauto.
Qed.

Lemma rtc_reverse
      A R (a b:A)
      (RTC: rtc R a b):
  rtc (fun x y => R y x) b a.
Proof.
  induction RTC; eauto.
  etrans; eauto.
Qed.

Lemma fapp A (B:A->Type) (a:A) (P Q:forall (a:A), B a)
      (EQ: P = Q):
  P a = Q a.
Proof. rewrite EQ. auto. Qed.

Inductive rtcn A (R: A -> A -> Prop): forall (n:nat) (a1 a2:A), Prop :=
| rtcn_nil
    a:
    rtcn R 0 a a
| rtcn_cons
    a1 a2 a3 n
    (A12: R a1 a2)
    (A23: rtcn R n a2 a3):
    rtcn R (S n) a1 a3
.
#[export]
Hint Constructors rtcn: core.

Lemma rtcn_rtc A (R: A -> A -> Prop) n a1 a2
      (RTCN: rtcn R n a1 a2):
  rtc R a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma rtc_rtcn A (R: A -> A -> Prop) a1 a2
      (RTC: rtc R a1 a2):
  exists n, rtcn R n a1 a2.
Proof.
  induction RTC; eauto. i. des.
  esplits; eauto.
Qed.

Lemma rtcn_imply
      A (R1 R2: A -> A -> Prop) n a1 a2
      (LE: forall a b, R1 a b -> R2 a b)
      (RTCN: rtcn R1 n a1 a2):
  rtcn R2 n a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma strong_induction
      (P : nat -> Prop)
      (IH: forall (n:nat) (IH: forall k (LT: k < n), P k), P n):
  forall n : nat, P n.
Proof.
  i. cut (forall m k, k < m -> P k); [by eauto|].
  induction m.
  - i. lia.
  - i. rewrite Nat.lt_succ_r Nat.succ_le_mono in H. inv H; eauto.
Qed.

Definition option_app {A} (a b: option A) : option A :=
  if a then a else b.

Definition option_rel {A B} (P: A -> B -> Prop) : option A -> option B -> Prop :=
  fun a b => match a, b with
             | Some x, Some y => P x y
             | None, None => True
             | _, _ => False end.

Definition option_rel_bool A B (f: A -> B -> bool) (a: option A) (b: option B): bool :=
  match a, b with
  | Some a, Some b => f a b
  | None, None => true
  | _, _ => false
  end.

Lemma option_rel_mon A B (R0 R1: A -> B-> Prop)
      (LE: forall a b (PR: R0 a b), R1 a b)
  :
    forall a b (PR: option_rel R0 a b), option_rel R1 a b.
Proof. i. unfold option_rel in *. des_ifs. auto. Qed.


Definition option_rel3 {A B C} (P: A -> B -> C -> Prop):
  option A -> option B -> option C -> Prop :=
  fun a b c => match a, b, c with
            | Some x, Some y, Some z => P x y z
            | None, None, None => True
            | _, _, _ => False
            end.

Lemma strengthen
      (A B: Prop)
      (H: A /\ (A -> B)):
  A /\ B.
Proof. intuition. Qed.

Lemma option_map_map
      A B C (f: B -> C) (g: A -> B) (a: option A):
  option_map f (option_map g a) = option_map (fun x => f (g x)) a.
Proof.
  destruct a; eauto.
Qed.

Definition is_some {A} (o:option A): bool :=
  match o with
  | Some _ => true
  | None => false
  end.
Coercion is_some: option >-> bool.

Ltac condtac :=
  match goal with
  | [|- context[if ?c then _ else _]] =>
    let COND := fresh "COND" in
    destruct c eqn:COND
  end.


Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.

Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_true:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = true -> P.
Proof.
  intros P Q a. destruct a; simpl. auto. congruence.
Qed.

Lemma orb_symm (a b: bool): orb a b -> orb b a.
Proof. destruct a,b; eauto. Qed.

#[export]
Hint Resolve orb_symm: core.


Lemma in_prod
      A B
      (a: A)
      (b: B)
      (l: list (A * B))
      (IN: List.In (a, b) l):
  List.In a (List.map (fun x => fst x) l).
Proof.
  revert a b IN. induction l; ss; i. des.
  - destruct a. ss. inv IN. esplits; eauto.
  - exploit IHl; eauto.
Qed.

Lemma in_prod_inv
      A B
      (a: A)
      (l: list (A * B))
      (IN: List.In a (List.map (fun x => fst x) l)):
  exists b, List.In (a, b) l.
Proof.
  revert a IN. induction l; ss; i. des.
  - destruct a. ss. subst. esplits; eauto.
  - exploit IHl; eauto. i. des. eauto.
Qed.

Lemma prod_in
      A B
      (a: A)
      (b: B)
      (l: list B)
      (IN: List.In b l):
  List.In (a, b) (List.map (fun x => (a, x)) l).
Proof.
  revert b IN. induction l; ss; i.
  des; subst; eauto.
Qed.

Lemma Forall_app
      A
      (P: A -> Prop)
      (l1 l2: list A)
      (FORALL1: List.Forall P l1)
      (FORALL2: List.Forall P l2):
  List.Forall P (l1 ++ l2).
Proof.
  induction l1; ss.
  inv FORALL1. eauto.
Qed.

Lemma Forall_app_inv
      A
      (P: A -> Prop)
      (l1 l2: list A)
      (FORALL: List.Forall P (l1 ++ l2)):
  <<FORALL1: List.Forall P l1>> /\
             <<FORALL2: List.Forall P l2>>.
Proof.
  induction l1; split; ss.
  - inv FORALL. exploit IHl1; eauto. i. des. eauto.
  - inv FORALL. exploit IHl1; eauto. i. des. ss.
Qed.

Lemma option_eq_dec
      A
      (X: forall x y: A, {x = y} + {x <> y}):
  forall x y: option A, {x = y} + {x <> y}.
Proof.
  i. destruct x, y; (try by left; ss); (try by right; ss).
  destruct (X a a0); subst; eauto.
  right. ii. inv H.
Qed.

Lemma pair_eq_dec
      A B
      (X: forall x y: A, {x = y} + {x <> y})
      (Y: forall x y: B, {x = y} + {x <> y}):
  forall x y: A * B,
    {fst x = fst y /\ snd x = snd y} +
    {fst x <> fst y \/ snd x <> snd y}.
Proof.
  i. destruct x, y. ss.
  destruct (X a a0); cycle 1.
  { right. left. ss. }
  destruct (Y b b0); cycle 1.
  { right. right. ss. }
  left. ss.
Qed.
