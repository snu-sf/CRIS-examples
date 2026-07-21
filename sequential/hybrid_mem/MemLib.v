From CRIS.common Require Import CRIS.
From CRIS.hybrid_mem Require Import MemHdr.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.


Module Mem.
  Record t : Type := mk {
    cnts : Z -> option val;
    next_loc : Z;
  }
  .

  Definition wf (m0 : t) : Prop := forall loc v, m0.(cnts) loc = Some v -> (0 < loc < m0.(next_loc))%Z.

  Definition update_cnts (m0 : Mem.t) (sz : Z) :=
    let nloc := m0.(next_loc) in
    fun loc =>
      if bool_decide (0 < loc)%Z
      then if bool_decide (loc < nloc)%Z then m0.(cnts) loc
           else if bool_decide (loc < nloc + sz)%Z then Some Vundef
                else None
      else None.

  Definition alloc (m0 : Mem.t) (sz : Z) : (Z * Mem.t) :=
    (m0.(next_loc), Mem.mk (update_cnts m0 sz) (m0.(next_loc) + sz))
  .

  Opaque Z.ltb Z.leb Z.mul Z.eq_dec Nat.eq_dec.

  Definition empty : t := mk (fun _ => None) 1.

  Definition free (m0 : Mem.t) := fun loc =>
    match m0.(cnts) loc with
    | Some _ => Some (Mem.mk (update (m0.(cnts)) loc None) m0.(next_loc))
    | _ => None
    end
  .

  Definition load (m0 : Mem.t) := fun loc =>
    m0.(cnts) loc.

  Definition store (m0 : Mem.t) := fun loc v =>
    match m0.(cnts) loc with
    | Some _ => Some (Mem.mk (update m0.(cnts) loc (Some v)) m0.(next_loc))
    | _ => None
    end
  .

  Definition valid_ptr (m0 : Mem.t) := fun loc =>
    match m0.(cnts) loc with
    | Some _ => true
    | None => false
    end.

  Definition vcmp (m0 : Mem.t) (x y : val) : option bool :=
    match x, y with
    | Vint x, Vint y =>
      if bool_decide (0 < x)%Z
      then
        if bool_decide (0 < y)%Z
        then if bool_decide (Mem.valid_ptr m0 x ∧ Mem.valid_ptr m0 y)
             then Some (bool_decide (x = y))
             else None
        else if bool_decide (y = 0)%Z
             then if bool_decide (Mem.valid_ptr m0 x) then Some false else None
             else None
      else
        if bool_decide (0 < y)%Z
        then if bool_decide (x = 0)%Z
             then if bool_decide (Mem.valid_ptr m0 y) then Some false else None
             else None
        else Some (bool_decide (x = y))
    | _, _ => None
    end.

  Definition mem_pad (m0 : Mem.t) (delta : nat) : Mem.t :=
    Mem.mk m0.(Mem.cnts) (m0.(Mem.next_loc) + Z.of_nat delta)
  .

End Mem.

Local Canonical Structure valO := leibnizO val.
Local Definition frac_valO := (dfrac_agreeR (optionO valO)).
Local Definition _memRA := (Z -d> optionUR frac_valO).
Local Definition memRA := authUR _memRA.
Class memGpreS `{!crisG Γ Σ α β τ _S _I} := {
    #[local] mem_inG :: inG memRA Γ;
  }.
Class memGS `{!crisG Γ Σ α β τ _S _I} := {
    #[local] memGS_memGSpreS :: memGpreS;
    mem_name : gname;
  }.
Definition memΓ : HRA := #[memRA].
Global Instance subG_memGS `{!crisG Γ Σ α β τ _S _I} : subG memΓ Γ → memGpreS.
Proof. solve_inG. Defined.

Section MEM.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition mem_init_auth_r : memRA :=
    (● ((λ loc, ε) : _memRA)).

  Definition mem_init_frag_r : memRA :=
    (◯ ((λ loc, ε) : _memRA)).

  Definition mem_init_auth : iProp Σ :=
    own mem_name (mem_init_auth_r).

  Definition mem_init_frag : iProp Σ :=
    own mem_name (mem_init_frag_r).

  Definition mem_init : iProp Σ :=
    own mem_name (mem_init_auth_r ⋅ mem_init_frag_r).

  Lemma mem_init_valid :
    ✓ (mem_init_auth_r ⋅ mem_init_frag_r).
  Proof. rewrite /mem_init_auth_r /mem_init_frag_r auth_both_valid_discrete; split; ii; des_ifs. Qed.

  Definition ir_memRA : DRA_mk memRA :=
    mem_init_auth_r ⋅ mem_init_frag_r.
  Lemma ir_memRA_valid : ✓ (ir_memRA).
  Proof. pose proof (mem_init_valid). rewrite /ir_memRA //. Qed.

End MEM.

Local Arguments Z.of_nat : simpl nomatch.

Section MemRA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition mem_val : Type := Qp * val.

  Definition _points_to_r (loc : Z) (q: Qp) (mvs : list val): _memRA :=
    fun loc0 =>
      if bool_decide (loc <= loc0 < (loc + Z.of_nat (List.length mvs)))%Z
      then match (List.nth_error mvs (Z.to_nat (loc0 - loc))) with
           | Some v => Some (to_frac_agree q (Some v))
           | None => ε
           end
      else ε.

  Definition mem_points_to_singleton_r (loc : Z) (q: Qp) (v : val) : memRA :=
    (◯ (discrete_fun_singleton loc (Some (to_frac_agree q (Some v))))).
  Definition mem_points_to_singleton (loc : Z) (q: Qp) (v : val) : iProp Σ :=
    own mem_name ((mem_points_to_singleton_r loc q v) : memRA).
  Definition mem_points_to : Z → Qp → list val → iProp Σ :=
    λ loc q vs, ([∗ list] i ↦ v ∈ vs, mem_points_to_singleton (loc + i)%Z q v)%I.

End MemRA.

Section syn_mem.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition syn_mem_points_to_singleton {n} loc q v : GTerm.t n :=
    sown mem_name ((mem_points_to_singleton_r loc q v) : memRA).

End syn_mem.

Notation "loc '⤇{' q '}' v" := (mem_points_to_singleton loc q v) (at level 20).
Notation "loc ⤇ v" := (mem_points_to_singleton loc 1 v) (at level 20).
Notation "loc ⤇ v" := (syn_mem_points_to_singleton loc 1 v)%SAT (at level 20) : SAT_scope.
Notation "loc |=> vs" := (mem_points_to loc 1 vs) (at level 20).

Global Opaque mem_points_to_singleton_r.
Arguments mem_points_to_singleton_r : simpl never.


(* Auxiliary Definitions & Lemmas *)
Section AUX.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_MEM: !memGS}.

  Fixpoint is_list (ll: val) (xs: list val): iProp Σ :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vint lhd ∧ (0 < lhd)%Z⌝ ∗ lhd |=> [xhd; ltl] ∗ is_list ltl xtl)%I
    end.

  Lemma unfold_is_list ll xs:
    is_list ll xs =
    match xs with
    | [] => (⌜ll = Vnullptr⌝)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vint lhd ∧ (0 < lhd)%Z⌝ ∗ lhd |=> [xhd; ltl] ∗ is_list ltl xtl)%I
    end.
  Proof using. destruct xs; ss. Qed.

  Lemma unfold_is_list_cons ll xhd xtl:
    is_list ll (xhd :: xtl) =
    (∃ lhd ltl, ⌜ll = Vint lhd ∧ (0 < lhd)%Z⌝ ∗ lhd |=> [xhd; ltl] ∗ is_list ltl xtl)%I.
  Proof using. eapply unfold_is_list. Qed.

  Lemma is_list_wf ll xs:
    (is_list ll xs) -∗ (⌜(ll = Vnullptr) ∨ (match ll with | Vint loc => (0 < loc)%Z | _ => False end)⌝).
  Proof using.
    iIntros "L". destruct xs; ss; et.
    { iPure "L" as L. iPureIntro. et. }
    iDestruct "L" as (? ?) "(% & P & L)". des.
    iPureIntro; right; subst; ss.
  Qed.

End AUX.

Section AUX2.

  Lemma repeat_nth_some X (x: X) sz ofs (IN: ofs < sz) :
    nth_error (repeat x sz) ofs = Some x.
  Proof using.
    ginduction sz; ii; ss.
    - lia.
    - destruct ofs; ss. exploit IHsz; et. lia.
  Qed.

  Lemma repeat_nth_none
    X (x: X) sz ofs
    (IN: ~(ofs < sz))
    :
    nth_error (repeat x sz) ofs = None
    .
  Proof using.
    generalize dependent ofs. induction sz; ii; ss.
    - destruct ofs; ss.
    - destruct ofs; ss. { lia. } hexploit (IHsz ofs); et. lia.
  Qed.

  Lemma nth_error_empty
    {X: Type} ofs
    :
    nth_error ([]: list X) ofs = None.
  Proof using.
    unfold nth_error. destruct ofs; ss.
  Qed.

  Lemma Z2nat_lt (x0: Z) (sz : nat)
    (ZLT: (x0 < sz)%Z)
    (SZ: (0 < sz))
  :
    (Z.to_nat x0 < sz).
  Proof using.
    induction sz.
    - lia.
    - induction x0.
      * ss.
      * ss.
      assert (Z.succ sz = sz + 1)%Z. ss.
      apply Z2Nat.inj_lt in ZLT; try lia.
      * ss.
  Qed.

  Lemma Z_ne_le (z1 : Z) (z2 : Z)
    (NE: z1 ≠ z2)
    (LE: (z1 <=? z2)%Z)
  :
    (z1 < z2)%Z.
  Proof using.
    apply Z.leb_le in LE.
    destruct (Z.eq_dec z1 z2) as [Heq | Hneq].
  - contradiction.
  - lia.
  Qed.

Lemma nth_lookup_Some_rev :
  ∀ (A : Type) (l : list A) (i : nat) (d x : A),
    i < length l →
    nth i l d = x →
    l !! i = Some x.
Proof.
  intros A l i d x Hi Hnth.
  revert i Hi Hnth.
  induction l as [|a l IH]; intros [|i] Hi Hnth; simpl in *; try lia.
  - inversion Hnth; reflexivity.
  - apply IH; try lia; exact Hnth.
Qed.

Lemma lookup_nth_inbounds :
  ∀ (A : Type) (l : list A) (i : nat) (d : A),
    i < length l →
    l !! i = Some (nth i l d).
Proof.
  intros A l i d Hi.
  apply nth_lookup_Some_rev with (d:=d).
  - exact Hi.
  - reflexivity.
Qed.

End AUX2.


Section RA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_MEM: !memGS}.

  Lemma split_points_to_r loc q a l :
    _points_to_r loc q (a :: l)
    ≡ (_points_to_r loc q [a]) ⋅ (_points_to_r (loc + 1)%Z q l).
  Proof using _MEM.
    intros loc0. rewrite !discrete_fun_lookup_op /= /_points_to_r.
    cbn [List.length].
    destruct (decide (loc0 = loc)) as [->|NE].
    - assert (BOOL0: bool_decide (loc <= loc < loc + Z.of_nat (S (List.length l)))%Z = true).
      { apply bool_decide_eq_true_2. rewrite Nat2Z.inj_succ. lia. }
      assert (BOOL1: bool_decide (loc <= loc < loc + Z.of_nat (S O))%Z = true).
      { apply bool_decide_eq_true_2. simpl. lia. }
      assert (BOOL2: bool_decide (loc + 1 <= loc < loc + 1 + Z.of_nat (List.length l))%Z = false).
      { apply bool_decide_eq_false_2. intros [? ?]. lia. }
      rewrite BOOL0 BOOL1 BOOL2 Z.sub_diag /= right_id //. 
    - destruct (Z_lt_ge_dec loc0 loc) as [LT|GE].
      + assert (BOOL0: bool_decide (loc <= loc0 < loc + Z.of_nat (S (List.length l)))%Z = false).
        { apply bool_decide_eq_false_2. intros [? ?]. lia. }
        assert (BOOL1: bool_decide (loc <= loc0 < loc + Z.of_nat (S O))%Z = false).
        { apply bool_decide_eq_false_2. intros [? ?]. lia. }
        assert (BOOL2: bool_decide (loc + 1 <= loc0 < loc + 1 + Z.of_nat (List.length l))%Z = false).
        { apply bool_decide_eq_false_2. intros [? ?]. lia. }
        rewrite BOOL0 BOOL1 BOOL2 //. 
      + assert (GT: (loc < loc0)%Z) by lia.
        assert (NEQ1: (loc + 1 <= loc0)%Z) by lia.
        destruct (Z_lt_ge_dec loc0 (loc + Z.of_nat (S (List.length l)))) as [IN|OUT].
        * assert (BOOL0: bool_decide (loc <= loc0 < loc + Z.of_nat (S (List.length l)))%Z = true).
          { apply bool_decide_eq_true_2. lia. }
          assert (BOOL1: bool_decide (loc <= loc0 < loc + Z.of_nat (S O))%Z = false).
          { apply bool_decide_eq_false_2. intros [? ?]. simpl in *. lia. }
          assert (BOOL2: bool_decide (loc + 1 <= loc0 < loc + 1 + Z.of_nat (List.length l))%Z = true).
          { apply bool_decide_eq_true_2. rewrite Nat2Z.inj_succ in IN. lia. }
          rewrite BOOL0 BOOL1 BOOL2 left_id.
          replace (loc0 - (loc + 1))%Z with (loc0 - loc - 1)%Z by nia.
          replace (Z.to_nat (loc0 - loc)) with (S (Z.to_nat (loc0 - loc - 1))) by nia.
          ss.
        * assert (BOOL0: bool_decide (loc <= loc0 < loc + Z.of_nat (S (List.length l)))%Z = false).
          { apply bool_decide_eq_false_2. intros [? ?]. lia. }
          assert (BOOL1: bool_decide (loc <= loc0 < loc + Z.of_nat (S O))%Z = false).
          { apply bool_decide_eq_false_2. intros [? ?]. simpl in *. lia. }
          assert (BOOL2: bool_decide (loc + 1 <= loc0 < loc + 1 + Z.of_nat (List.length l))%Z = false).
          { apply bool_decide_eq_false_2. intros [? ?]. rewrite Nat2Z.inj_succ in OUT. lia. }
          rewrite BOOL0 BOOL1 BOOL2 //. 
  Qed.

  Lemma points_to_singleton loc q a :
    _points_to_r loc q [a]
    ≡ (discrete_fun_singleton loc (Some (to_frac_agree q (Some a)))).
  Proof using _MEM.
    intros loc0. unfold _points_to_r. ss.
    case_bool_decide as RANGE.
    - assert (loc0 = loc) by nia. subst.
      rewrite Z.sub_diag /= discrete_fun_lookup_singleton //. 
    - destruct (decide (loc0 = loc)) as [EQ|NE].
      + subst. exfalso. apply RANGE. nia.
      + rewrite discrete_fun_lookup_singleton_ne //.
  Qed.

  Local Transparent mem_points_to_singleton_r.

  Lemma points_to_transform loc q l :
    own mem_name (((◯ _points_to_r loc q l)) : memRA)
    ⊢ [∗ list] i↦v ∈ l, (loc + i)%Z ⤇{q} v.
  Proof using _MEM.
    gen loc. induction l.
    - iIntros; eauto.
    - i. rewrite split_points_to_r. iIntros "[P L]".
      rewrite big_sepL_cons. rewrite points_to_singleton.
      iPoseProof (IHl with "L") as "L".
      set (λ _ _, _). set (λ _ _, _).
      assert (y = y0).
      { extensionalities. subst y y0. ss.
        replace (loc + 1 + H)%Z with (loc + S H)%Z by nia. refl. }
      rewrite H. iFrame. unfold mem_points_to_singleton, mem_points_to_singleton_r; ss.
      rewrite Z.add_0_r. iFrame.
  Qed.

  Lemma to_frac_agree_inv A q (v: leibnizO A) f
    (EQ: to_frac_agree q (Some v) ≡ f)
    :
    f.1 = DfracOwn q ∧ ∃ tl, f.2.(agree_car) = (Some v) :: tl.
  Proof using.
    rr in EQ. des. ss. rr in EQ. rewrite EQ; split; et.
    specialize (EQ0 0). rr in EQ0. des.
    edestruct EQ0; s; eauto using elem_of_list.
    des. ss. destruct (agree_car f.2) eqn: E.
    - rewrite E in H. rr in H. inv H.
    - exists l. destruct x; cycle 1.
      { inv H0. }
      f_equal. inv H0. rr in H3. depdes H3. rewrite E in EQ1.
      edestruct (EQ1 o); eauto using elem_of_list. des.
      destruct x; cycle 1.
      { inv H0. inv H4. }
      inv H0; ss; cycle 1.
      { inv H4. }
      destruct o; cycle 1.
      { inv H1. }
      inv H1.
      rr in H3. depdes H3. refl.
  Qed.

  Lemma to_frac_full_valid_inv A c (v: leibnizO A)
    (VALID: ✓ (Some (to_frac_agree 1 (Some v)) ⋅ c))
    :
    c = None.
  Proof using.
    destruct c; et. rewrite -?Some_op in VALID.
    rr in VALID. des. ss. exfalso. eapply dfrac_full_exclusive; et.
  Qed.

  Definition mem_own (g : gname) (r: memRA) := own g r.

End RA.

Lemma mem_alloc `{!crisG Γ Σ α β τ Hsub Hinv, _MEMPRE: !memGpreS} :
  ⊢ o=> ∃ (_ : memGS), mem_init.
Proof.
  iMod (own_alloc (mem_init_auth_r ⋅ mem_init_frag_r)) as "[%γm M]".
  { apply ir_memRA_valid. }
  pose (@Build_memGS _ _ _ _ _ _ _ _ _ γm) as Hmem.
  rewrite /mem_init.
  by iExists Hmem; iFrame.
Qed.
