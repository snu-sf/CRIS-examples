From Stdlib Require Import Orders.

Require Import DataStructure.
Require Export DenseOrder.
Require Import Basic.
Require Import Loc.

From CRIS.lib Require Import sflib Coqlib.

Set Implicit Arguments.


Module Time.
  Include DenseOrder.
  
  Definition init : t := incr bot.

  Definition init_spec : lt bot init.
  Proof. econs. Qed.
End Time.

Module TimeFacts := DenseOrderFacts.

Ltac timetac :=
  repeat
    (try match goal with
         | [|- Time.le Time.bot ?x] => apply Time.bot_spec
         | [H: Time.lt ?x Time.bot |- _] => sfby inv H
         | [H: Some _ = None |- _] => inv H
         | [H: None = Some _ |- _] => inv H
         | [H: ?x <> ?x |- _] => sfby contradict H
         | [H: Time.lt ?x ?x |- _] =>
           apply Time.lt_strorder in H; sfby inv H
         | [H1: Time.lt ?a ?b, H2: Time.lt ?b ?a |- _] =>
           rewrite H1 in H2; apply Time.lt_strorder in H2; sfby inv H2
         | [H1: Time.lt ?a ?b, H2: Time.le ?b ?a |- _] =>
           exploit (@TimeFacts.lt_le_lt a b a); eauto;
           let H := fresh "H" in
           intro H; apply Time.lt_strorder in H; sfby inv H
         | [H1: Time.le ?a ?b, H2: Time.lt ?b ?c |- Time.lt ?a ?c] =>
             eapply TimeFacts.le_lt_lt; try exact H1; try exact H2
         | [H1: Time.lt ?a ?b, H2: Time.le ?b ?c |- Time.lt ?a ?c] =>
             eapply TimeFacts.lt_le_lt; try exact H1; try exact H2
         | [H: Time.lt ?a ?b |- Time.le ?a ?b] =>
             left; apply H

         | [H: Some _ = Some _ |- _] => inv H

         | [H: context[Time.eq_dec ?a ?b] |- _] =>
           destruct (Time.eq_dec a b)
         | [H: context[TimeFacts.le_lt_dec ?a ?b] |- _] =>
           destruct (TimeFacts.le_lt_dec a b)
         | [|- context[Time.eq_dec ?a ?b]] =>
           destruct (Time.eq_dec a b)
         | [|- context[TimeFacts.le_lt_dec ?a ?b]] =>
           destruct (TimeFacts.le_lt_dec a b)
         end;
     ss; subst; auto).

Ltac ett := eapply TimeFacts.le_lt_lt.
Ltac tet := eapply TimeFacts.lt_le_lt.

Module TimeSet := UsualSet Time.
Module TimeFun := UsualFun Time.

Module Interval <: UsualOrderedType.
  Include UsualProd Time Time.

  Variant mem (interval:t) (x:Time.t): Prop :=
  | mem_intro
      (FROM: Time.lt (fst interval) x)
      (TO: Time.le x (snd interval))
  .

  Lemma mem_dec i x: {mem i x} + {~ mem i x}.
  Proof.
    destruct i as [lb ub].
    destruct (TimeFacts.le_lt_dec x lb).
    - right. intro X. inv X. ss. timetac.
    - destruct (TimeFacts.le_lt_dec x ub).
      + left. econs; s; auto.
      + right. intro X. inv X. ss. timetac.
  Defined.

  Variant le (lhs rhs:t): Prop :=
  | le_intro
      (FROM: Time.le (fst rhs) (fst lhs))
      (TO: Time.le (snd lhs) (snd rhs))
  .

  Lemma le_mem lhs rhs x
        (LE: le lhs rhs)
        (LHS: mem lhs x):
    mem rhs x.
  Proof.
    inv LE. inv LHS. econs.
    - eapply TimeFacts.le_lt_lt; eauto.
    - etrans; eauto.
  Qed.

  Lemma mem_ub
        lb ub (LT: Time.lt lb ub):
    mem (lb, ub) ub.
  Proof.
    econs; s; auto. refl.
  Qed.

  Definition disjoint (lhs rhs:t): Prop :=
    forall x
      (LHS: mem lhs x)
      (RHS: mem rhs x),
      False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eapply H; eauto.
  Qed.

  Lemma disjoint_imm a b c:
    disjoint (a, b) (b, c).
  Proof.
    ii. inv LHS. inv RHS. ss.
    eapply DenseOrder.lt_strorder.
    eapply TimeFacts.le_lt_lt; [apply TO|apply FROM0].
  Qed.

  Lemma le_disjoint
        a b c
        (DISJOINT: disjoint b c)
        (LE: le a b):
    disjoint a c.
  Proof.
    ii. eapply DISJOINT; eauto. eapply le_mem; eauto.
  Qed.

  Definition valid (i : t) : Prop := Time.lt (fst i) (snd i).

  Lemma mem_imp_valid i x (H: mem i x) : valid i.
  Proof.
    inv H. eapply TimeFacts.lt_le_lt; eauto.
  Qed.

  Lemma disjoint_imp_le
        a b c d
        (DISJOINT: disjoint (a, b) (c, d))
        (VALID1: valid (a, b))
        (VALID2: valid (c, d)):
    (Time.le b c \/ Time.le d a).
  Proof.
    unfold valid in *.
    destruct (Time.le_lt_dec b c). sfby left.
    destruct (Time.le_lt_dec d a). sfby right.
    exfalso.
    
    set (lb_overlap := Time.max a c). 
    set (ub_overlap := Time.meet b d).
    assert (H_overlap_valid : Time.lt lb_overlap ub_overlap).
    { unfold Time.max, Time.meet in *.
      destruct (Time.le_lt_dec a c); destruct (Time.le_lt_dec b d).
      all: (inv l1; inv l2; ss).
    }

    apply Time.middle_spec in H_overlap_valid.
    apply (DISJOINT (Time.middle lb_overlap ub_overlap)); econs; ss.
    { unfold Time.max, Time.meet in *.
      destruct (Time.le_lt_dec a c); destruct (Time.le_lt_dec b d).
      1, 2: ett; eauto; sfby inv H_overlap_valid.
      1, 2: sfby inv H_overlap_valid.
    }
    { unfold Time.max, Time.meet in *.
      destruct (Time.le_lt_dec a c); destruct (Time.le_lt_dec b d).
      { inv l1; inv l2; inv H_overlap_valid; rewrite Time.le_lteq; sfby left. }
      { inv l1; inv H_overlap_valid; rewrite Time.le_lteq; left; ett.
        rewrite Time.le_lteq; left. eauto. eauto.
        rewrite Time.le_lteq; left. eauto. eauto.
      }
      { inv l2; inv H_overlap_valid; rewrite Time.le_lteq; left; ett.
        rewrite Time.le_lteq; right. eauto. eauto.
        rewrite Time.le_lteq; right. eauto. eauto.
      }
      { inv H_overlap_valid; rewrite Time.le_lteq; left; ett.
        rewrite Time.le_lteq; left. eauto. eauto.
      }
    }
    { unfold Time.max, Time.meet in *.
      destruct (Time.le_lt_dec a c); destruct (Time.le_lt_dec b d).
      1, 2: sfby inv H_overlap_valid.
      1, 2: tet; eauto; rewrite Time.le_lteq; left; sfby inv H_overlap_valid.
    }
    { unfold Time.max, Time.meet in *.
      destruct (Time.le_lt_dec a c); destruct (Time.le_lt_dec b d).
      { inv l1; inv l2; inv H_overlap_valid; rewrite Time.le_lteq; left; eauto.
        tet; eauto; rewrite Time.le_lteq; sfby right.
        tet; eauto; rewrite Time.le_lteq; sfby right.
      }
      { inv l1; inv H_overlap_valid; rewrite Time.le_lteq; left; eauto. }
      { inv l2; inv H_overlap_valid; rewrite Time.le_lteq; left; eauto.
        tet; eauto; rewrite Time.le_lteq; sfby right.
      }
      { inv H_overlap_valid; rewrite Time.le_lteq; sfby left. }   
    }
  Qed.

  Lemma disjoint_lt_valid
        a b c d
        (DISJOINT: disjoint (a, b) (c, d))
        (VALID1: valid (a, b))
        (VALID2: valid (c, d)):
    Time.lt b d \/ Time.lt d b.
  Proof.
    assert (H_le: Time.le b c \/ Time.le d a).
    { eapply disjoint_imp_le; eauto. }

    destruct H_le as [Hle_bc | Hle_da].
    - unfold valid in VALID2.
      left.
      eapply TimeFacts.le_lt_lt; eauto.
    - right.
      unfold valid in VALID1.
      eapply TimeFacts.le_lt_lt; eauto.
  Qed.
End Interval.


