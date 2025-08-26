Require Import CRIS.
Require Export ImpPrelude.

Module MutHdr.
  Definition mutf := "MutF.f".
  Definition mutg := "MutG.g".
End MutHdr.

Module MutAUX. Section MutAUX.

  Fixpoint sum (n: nat): nat :=
    match n with
    | O => O
    | S m => n + sum m
    end.
  (* Compute (sum 10). *)

  Definition mut_max: nat := 1000%nat.

  Lemma mut_max_intrange x
    (LT: x < mut_max)
    :
    intrange_64 x.
  Proof.
    unfold mut_max in *. unfold_intrange_64. rewrite two_power_nat_S.
    replace (2 * two_power_nat 63)%Z with ((two_power_nat 63) * 2)%Z.
    2:{ rewrite Z.mul_comm. lia. }
    unfold two_power_nat. ss.
    unfold sumbool_to_bool. des_ifs; try lia.
    all: rewrite ->Z.div_mul in *; try lia.
  Qed.

  Lemma mut_max_intrange_sub1 x
    (LT: x < mut_max)
    :
    intrange_64 (x - 1).
  Proof.
    unfold mut_max in *. unfold_intrange_64. rewrite two_power_nat_S.
    replace (2 * two_power_nat 63)%Z with ((two_power_nat 63) * 2)%Z.
    2:{ rewrite Z.mul_comm. lia. }
    unfold two_power_nat. ss.
    unfold sumbool_to_bool. des_ifs; try lia.
    all: rewrite -> Z.div_mul in *; try lia.
  Qed.

  Lemma mut_max_sum_intrange x
    (LT: x < mut_max)
    :
    intrange_64 (sum x).
  Proof.
    cut (sum x <= mut_max * mut_max)%Z.
    { unfold mut_max.
      generalize (sum x). clear LT. intros n LT.
      unfold_intrange_64. rewrite two_power_nat_S.
      replace (2 * two_power_nat 63)%Z with ((two_power_nat 63) * 2)%Z.
      2:{ rewrite Z.mul_comm. lia. }
      unfold two_power_nat. ss.
      unfold sumbool_to_bool. des_ifs; try lia.
      all: rewrite -> Z.div_mul in *; try lia.
    }
    cut (sum x <= x * x).
    { nia. }
    induction x; ss. lia.
  Qed.

End MutAUX. End MutAUX.