Require Import CRIS.common.CRIS.
From CRIS.promise_free.lib Require Import Val Loc.

Module StackHdr.
  (** Physical payloads must never be [Vundef]: promise-free non-atomic reads
      may refine an undefined cell to any value.  This total encoding reserves
      zero for [Vundef] and maps numeric payloads to odd integers. *)
  Definition encode (v : Val.t) : Val.t :=
    match v with
    | Val.Vnum z => Val.Vnum (2 * z + 1)%Z
    | Val.Vptr l => Val.Vptr l
    | Val.Vundef => Val.Vnum 0
    end.

  Definition decode (v : Val.t) : Val.t :=
    match v with
    | Val.Vnum z =>
        if (z =? 0)%Z then Val.Vundef else Val.Vnum ((z - 1) / 2)%Z
    | Val.Vptr l => Val.Vptr l
    | Val.Vundef => Val.Vundef
    end.

  Lemma decode_encode v : decode (encode v) = v.
  Proof.
    destruct v as [z|l|]; simpl; [|done|done].
    assert (NZ : (2 * z + 1 =? 0)%Z = false).
    { apply Z.eqb_neq. lia. }
    rewrite NZ. f_equal.
    replace (2 * z + 1 - 1)%Z with (z * 2)%Z by ring.
    apply Z.div_mul. lia.
  Qed.

  Lemma encode_not_undef v : encode v <> Val.Vundef.
  Proof. destruct v; simpl; congruence. Qed.

  Lemma le_defined_eq {v' v}
      (DEFINED : v <> Val.Vundef) (LE : Val.le v' v) :
    v' = v.
  Proof.
    destruct v as [z|l|], v' as [z'|l'|]; ss.
    - apply Z.eqb_eq in LE. subst. done.
    - apply Loc.eqb_eq in LE. subst. done.
  Qed.

  Lemma le_encode_eq {v' v} (LE : Val.le v' (encode v)) :
    v' = encode v.
  Proof. eapply le_defined_eq; [apply encode_not_undef|exact LE]. Qed.

  Lemma decode_le_encode {v' v} (LE : Val.le v' (encode v)) :
    decode v' = v.
  Proof. rewrite (le_encode_eq LE). apply decode_encode. Qed.

  Lemma encode_injective v1 v2 (EQ : encode v1 = encode v2) :
    v1 = v2.
  Proof.
    apply (f_equal decode) in EQ. by rewrite !decode_encode in EQ.
  Qed.

  Lemma le_vptr_eq {v' l} (LE : Val.le v' (Val.Vptr l)) :
    v' = Val.Vptr l.
  Proof. eapply le_defined_eq; [congruence|exact LE]. Qed.

  Definition new_stack := fnsig "PFElimStack.new_stack" (fntyp () Val.t).
  Definition push := fnsig "PFElimStack.push" (fntyp (Val.t * Val.t) Val.t).
  Definition pop := fnsig "PFElimStack.pop" (fntyp Val.t Val.t).
End StackHdr.
