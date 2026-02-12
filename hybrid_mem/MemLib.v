From CRIS Require Import CRIS.
Require Import MemHdr.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.


Module Mem.
  (* Definition t : Type := mblock -> option (Z -> val). *)
  Record t : Type := mk {
    cnts : mblock -> Z -> option val;
    nb : mblock;
  }
  .

  Definition wf (m0 : t) : Prop := forall blk ofs (LT : (blk < m0.(nb))%nat), m0.(cnts) blk ofs = None.

  Definition alloc (m0 : Mem.t) (sz : Z) : (mblock * Mem.t) :=
    ((m0.(nb)),
     Mem.mk (update (m0.(cnts)) (m0.(nb))
                    (fun ofs => if (0 <=? ofs)%Z && (ofs <? sz)%Z then Some (Vundef) else None))
            (S m0.(nb))
    )
  .

  Opaque Z.ltb Z.leb Z.mul Z.eq_dec Nat.eq_dec.

  Definition empty : t := mk (fun _ _ => None) 0.

  Definition free (m0 : Mem.t) := fun '(b,ofs) =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (update m0.(cnts) b (update (m0.(cnts) b) ofs None)) m0.(nb))
    | _ => None
    end
  .

  Definition load (m0 : Mem.t) := fun '(b,ofs) =>
    m0.(cnts) b ofs.

  Definition store (m0 : Mem.t) := fun '(b,ofs) v =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (fun _b _ofs => if (dec b _b) && (dec ofs _ofs)
                                             then Some v
                                             else m0.(cnts) _b _ofs) m0.(nb))
    | _ => None
    end
  .

  Definition valid_ptr (m0 : Mem.t) := fun '(b,ofs) =>
    is_some (m0.(cnts) b ofs).

  Definition vcmp (m0 : Mem.t) (x y : val) : option bool :=
    match x, y with
    | Vint x, Vint y => Some (dec x y : bool)
    | Vptr (x, xofs), Vptr (y, yofs) =>
      if Mem.valid_ptr m0 (x, xofs) && Mem.valid_ptr m0 (y, yofs)
      then Some (dec x y && dec xofs yofs)
      else None
    | Vptr (x, xofs), Vint y =>
      if Mem.valid_ptr m0 (x, xofs) && dec y 0%Z
      then Some false
      else None
    | Vint x, Vptr (y, yofs) =>
      if Mem.valid_ptr m0 (y, yofs) && dec x 0%Z
      then Some false
      else None
    | _, _ => None
    end.

  Definition mem_pad (m0 : Mem.t) (delta : nat) : Mem.t :=
    Mem.mk m0.(Mem.cnts) (m0.(Mem.nb) + delta)
  .

End Mem.

Local Canonical Structure valO := leibnizO val.
Local Definition frac_valO := (dfrac_agreeR (optionO valO)).
Local Definition _memRA := (mblock -d> Z -d> optionUR frac_valO).
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
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition mem_init_auth_r : memRA :=
    (● ((λ blk ofs, ε): _memRA)).

  Definition mem_init_frag_r : memRA :=
    (◯ ((λ blk ofs, ε) : _memRA)).

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
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition mem_val : Type := Qp * val.

  Definition _points_to_r (loc : mblock * Z) (q: Qp) (mvs : list val): _memRA :=
    let (b, ofs) := loc in
    fun _b _ofs =>
      if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length mvs))))%Z
      then match (List.nth_error mvs (Z.to_nat (_ofs - ofs))) with
        | Some v => Some (to_frac_agree q (Some v))
        | None => ε
        end
      else ε.

  Definition mem_points_to_singleton_r (loc : mblock * Z) (q: Qp) (v : val) : memRA :=
    (◯ (discrete_fun_singleton loc.1 (discrete_fun_singleton loc.2 (Some (to_frac_agree q (Some v)))))).
  Definition mem_points_to_singleton (loc : mblock * Z) (q: Qp) (v : val) : iProp Σ :=
    own mem_name ((mem_points_to_singleton_r loc q v): memRA).
  Definition mem_points_to : (mblock * Z) → Qp → list val → iProp Σ :=
    λ '(blk, ofs) q vs, ([∗ list] i ↦ v ∈ vs, mem_points_to_singleton (blk, ofs + i)%Z q v)%I.

End MemRA.

Section syn_mem.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition syn_mem_points_to_singleton {n} loc q v : GTerm.t n :=
    sown mem_name ((mem_points_to_singleton_r loc q v): memRA).

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
  Context `{_memGS: !memGS}.

  Fixpoint is_list (ll: val) (xs: list val): iProp Σ :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr (lhd, 0%Z)⌝ ∗ (lhd, 0%Z) |=> [xhd; ltl] ∗ is_list ltl xtl)%I
    end.

  Lemma unfold_is_list ll xs:
    is_list ll xs =
    match xs with
    | [] => (⌜ll = Vnullptr⌝)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr (lhd, 0%Z)⌝ ∗ (lhd, 0%Z) |=> [xhd; ltl] ∗ is_list ltl xtl)%I
    end.
  Proof using. destruct xs; ss. Qed.

  Lemma unfold_is_list_cons ll xhd xtl:
    is_list ll (xhd :: xtl) =
    (∃ lhd ltl, ⌜ll = Vptr (lhd, 0%Z)⌝ ∗ (lhd, 0%Z) |=> [xhd; ltl] ∗ is_list ltl xtl)%I.
  Proof using. eapply unfold_is_list. Qed.

  Lemma is_list_wf ll xs:
    (is_list ll xs) -∗ (⌜(ll = Vnullptr) ∨ (match ll with | Vptr (_, 0%Z) => True | _ => False end)⌝).
  Proof using.
    iIntros "L". destruct xs; ss; et.
    { iPure "L" as L. iPureIntro. et. }
    iDestruct "L" as (? ?) "(% & P & L)".
    iPureIntro; right; subst; ss.
  Qed.

End AUX.

Ltac Ztac := all_once_fast ltac:(fun H => first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]).

Section AUX2.
  (* Context `{!crisG Γ Σ α β τ _S _I}. *)

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
  - (* Case: z1 = z2 (contradiction) *)
    contradiction.
  - (* Case: z1 ≠ z2 *)
    lia.
  Qed. (* Use NE and LE to conclude (z1 < z2)%Z *)

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
  Context `{_memGS: !memGS}.

  Lemma split_points_to_r blk ofs q a l :
    _points_to_r (blk, ofs) q (a :: l)
    ≡ (_points_to_r (blk, ofs) q [a]) ⋅ (_points_to_r (blk, (ofs+1)%Z) q l).
  Proof using _memGS.
    intros b o. rewrite !discrete_fun_lookup_op. ss.
    destruct (dec b blk).
    - subst. destruct (dec o ofs).
      + subst. ss. des_ifs; bsimpl; des; Ztac; try nia.
        { rewrite right_id. rewrite ->Z.sub_diag in *. ss. inv Heq0. ss. }
        { rewrite ->Z.sub_diag in *; ss. }
        { rewrite ->Z.sub_diag in *; ss. }
      + des_ifs; bsimpl; des; Ztac; try nia.
        { rewrite left_id. replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z  in Heq3 by nia.
          replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) in Heq0 by nia.
          ss. rewrite Heq0 in Heq3. inv Heq3. ss. }
        { replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z  in Heq3 by nia.
          replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) in Heq0 by nia.
          ss. rewrite Heq0 in Heq3. inv Heq3. }
        { replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z  in Heq3 by nia.
          replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) in Heq0 by nia.
          ss. rewrite Heq0 in Heq3. inv Heq3. }
    - des_ifs.
  Qed.

  Lemma points_to_singleton blk ofs q a :
    _points_to_r (blk, ofs) q [a]
    ≡ (discrete_fun_singleton blk (discrete_fun_singleton ofs (Some (to_frac_agree q (Some a))))).
  Proof using _memGS.
    intros b o. ss. des_ifs; destruct dec; bsimpl; des; Ztac; try nia.
    - replace o with ofs in * by nia. rewrite Z.sub_diag in Heq0. ss. inv Heq0.
      rewrite !discrete_fun_lookup_singleton //.
    - replace o with ofs in * by nia. rewrite Z.sub_diag in Heq0. ss.
    - subst. rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; [eauto|nia].
    - subst. rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; [eauto|nia].
    - rewrite discrete_fun_lookup_singleton_ne; eauto.
  Qed.

  Local Transparent mem_points_to_singleton_r.

  Lemma points_to_transform blk ofs q l :
    own mem_name (((◯ _points_to_r (blk, ofs) q l)): memRA)
    ⊢ [∗ list] i↦v ∈ l, (blk, (ofs + i)%Z) ⤇{q} v.
  Proof using _memGS.
    gen ofs. induction l.
    - iIntros; eauto.
    - i. rewrite split_points_to_r. iIntros "[P L]".
      rewrite big_sepL_cons. rewrite points_to_singleton.
      iPoseProof (IHl with "L") as "L".
      set (λ _ _, _). set (λ _ _, _).
      assert (y = y0).
      { extensionalities. subst y y0. ss.
        replace (ofs + 1 + H)%Z with (ofs + S H)%Z by nia. refl. }
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

  (*** Auxiliary constructor for MemDHProof ***)
  Definition mem_own (g : gname) (r: memRA) := own g r.

End RA.

Lemma mem_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !memGpreS} :
  ⊢ o=> ∃ (_ : memGS), mem_init.
Proof.
  iMod (own_alloc (mem_init_auth_r ⋅ mem_init_frag_r)) as "[%γm M]".
  { apply ir_memRA_valid. }
  pose (@Build_memGS _ _ _ _ _ _ _ _ _ γm) as Hmem.
  rewrite /mem_init.
  by iExists Hmem; iFrame.
Qed.
