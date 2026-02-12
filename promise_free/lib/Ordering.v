Require Import List.
Require Import Orders.
Require Import MSetList.
Require Import ZArith.

Require Import sflib.

Require Import DataStructure.
Require Import Basic.
Require Import Loc.
Require Import Language.
Require Import Val.

Set Implicit Arguments.

Module Ordering.
  (* NOTE: we curently do not support the nonatomics (#61).  Nonatomic
     accesses differ from plain accesses in that nonatomic accesses may
     corrupt data in the presence of a race.

     Even in Java, a data race may result in out-of-thin-air integral
     values.  But even with data races, it is impossible to forge an
     out-of-thin-air reference values.  See the link for more details:
     https://docs.oracle.com/javase/specs/jls/se7/html/jls-17.html#jls-17.7

     Hence, our compilation scheme for Java normal accesses is as
     follows.
     - Normal accesses to pointers are compiled to plain accesses.
     - Normal accesses to numbers are compiled to nonatomic accesses.
   *)
  Inductive t :=
  | na
  | relaxed
  | strong_relaxed
  | acqrel
  | seqcst
  .

  Definition le (lhs rhs:t): bool :=
    match lhs, rhs with
    | na, _ => true
    | _, na => false

    | relaxed, _ => true
    | _, relaxed => false

    | strong_relaxed, _ => true
    | _, strong_relaxed => false

    | acqrel, _ => true
    | _, acqrel => false

    | seqcst, seqcst => true
    end.
  Global Opaque le.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; auto.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; auto.
  Qed.
  #[global] Hint Resolve le_PreOrder_obligation_2: core.

  Definition join (lhs rhs:t): t :=
    match lhs, rhs with
    | na, _ => rhs
    | _, na => lhs

    | relaxed, _ => rhs
    | _, relaxed => lhs

    | strong_relaxed, _ => rhs
    | _, strong_relaxed => lhs

    | acqrel, _ => rhs
    | _, acqrel => lhs

    | seqcst, _ => rhs
    end.

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof. destruct a, b, c; ss. Qed.

  Lemma join_l lhs rhs:
    le lhs (join lhs rhs).
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_r lhs rhs:
    le rhs (join lhs rhs).
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_cases lhs rhs:
    join lhs rhs = lhs \/ join lhs rhs = rhs.
  Proof. destruct lhs, rhs; auto. Qed.
End Ordering.

