Require Import CRIS.
Require Export MapHeader MapM.

(* Resource algebra for MapM ⊆ MapA *)
Local Definition RA := prodUR (optionUR (exclR unitO)) (authUR (Z -d> optionUR (exclR ZO))).

Class mapGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] map_inG :: inG RA Γ;
}.
Class mapGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mapGS_mapGpreS :: mapGpreS;
  map_name : gname;
}.
Definition mapΓ : HRA := #[RA].
Global Instance subG_mapGpreS `{!crisG Γ Σ α β τ _S _I} : subG mapΓ Γ → mapGpreS.
Proof. solve_inG. Defined.

Module MapA. Section MapA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _MAP: !mapGS, _MAPM: !mapMGS}.

  Definition pending : iProp Σ := own map_name (Some (Excl ()), ε).

  Local Definition initial_fun : Z -d> optionUR (exclR ZO) := λ z, Some (Excl 0%Z).
  Definition initial_map : iProp Σ := own map_name (ε, ● initial_fun ⋅ ◯ initial_fun).

  Definition auth_allocated (f : Z → Z) : iProp Σ :=
    own map_name (ε, ● ((λ k, Some (Excl (f k))) : Z -d> optionUR (exclR ZO))).
  Definition auth_unallocated (sz : Z) : iProp Σ :=
    own map_name
      (ε,
      ◯ ((λ k,
        if (Z_gt_le_dec 0 k)
        then Some (Excl 0%Z)
        else if (Z_gt_le_dec sz k) then ε else Some (Excl 0%Z)) : Z -d> optionUR (exclR ZO)))%Z.
  Definition points_to (k v : Z) : iProp Σ :=
    own map_name (ε, ◯ (discrete_fun_singleton k (Some (Excl v)))).
  Definition initial_points_tos (sz : nat) : iProp Σ :=
    ([∗ list] i↦v ∈ (repeat (0 : Z) sz), points_to i%Z v)%I.

  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof using.
    iIntros "P P'"; iCombine "P P'" as "P" gives %FALSE.
    rewrite -pair_op pair_valid in FALSE; des; ss.
  Qed.

  Lemma initialize (sz : nat) :
    initial_map ==∗ auth_allocated (λ _ : Z, 0%Z) ∗ auth_unallocated sz ∗ initial_points_tos sz.
  Proof using.
    induction sz; ss.
    { iIntros "[I1 I2]"; iSplitL "I1"; first iModIntro; iFrame.
      iSplitL; last iModIntro; ss; last rewrite /initial_points_tos //=.
      iApply (own_update with "I2").
      apply prod_update; ss.
      rewrite cmra_update_proper; try reflexivity.
      f_equiv. ii; des_ifs; lia.
    }
    { iIntros "I"; iMod (IHsz with "I") as "[I1 [I2 I3]]".
      replace (S sz) with (sz + 1); last by lia.
      rewrite /initial_points_tos repeat_app big_opL_app repeat_length; ss.
      iSplitL "I1"; first by iModIntro; iFrame.
      iMod (own_update with "I2") as "[I1 I2]"; cycle 1.
      { iModIntro; iFrame. }
      rewrite -pair_op -auth_frag_op right_id; apply prod_update; ss.
      rewrite cmra_update_proper; try reflexivity.
      f_equiv; ii; rewrite discrete_fun_lookup_op; des_ifs; ss; try lia;
        try by rewrite discrete_fun_lookup_singleton_ne; ss; lia.
      assert (x = sz + 0) by lia; subst.
      rewrite discrete_fun_lookup_singleton; ss.
    }
  Qed.

  Lemma initial_map_points_to k v : initial_map -∗ points_to k v -∗ False.
  Proof using.
    rewrite /initial_map /points_to /initial_fun.
    iIntros "[I1 I2] PT"; iCombine "I2" "PT" as "I" gives %FALSE.
    rewrite -pair_op pair_valid /= -auth_frag_op auth_frag_valid in FALSE.
    destruct FALSE as [_ FALSE]. specialize (FALSE k); ss.
    rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton //= in FALSE.
  Qed.

  Lemma auth_unallocated_points_to sz k v : auth_unallocated sz -∗ points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
  Proof using.
    rewrite /auth_unallocated /points_to.
    iIntros "I PT"; iCombine "I" "PT" as "I" gives %wf.
    rewrite -pair_op pair_valid /= -auth_frag_op auth_frag_valid in wf.
    destruct wf as [_ wf]. specialize (wf k); ss.
    rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton //= in wf.
    des_ifs; ss. iPureIntro; lia.
  Qed.

  Lemma auth_allocated_get f k v : auth_allocated f -∗ points_to k v -∗ ⌜f k = v⌝.
  Proof using.
    rewrite /auth_allocated /points_to.
    iIntros "A P"; iCombine "A" "P" as "A" gives %wf.
    rewrite -pair_op pair_valid auth_both_valid_discrete /= in wf; des.
    apply (discrete_fun_included_spec_1 _ _ k) in wf0; ss; rewrite discrete_fun_lookup_singleton in wf0.
    rewrite Excl_included in wf0; inv wf0; ss.
  Qed.

  Lemma auth_allocated_set f k v w :
    auth_allocated f -∗ points_to k w ==∗ auth_allocated (<[k := v]> f) ∗ points_to k v.
  Proof using.
    rewrite /auth_allocated /points_to.
    iIntros "AU PT"; iCombine "AU" "PT" as "AU".
    iMod (own_update with "AU") as "[AU PT]"; last by iModIntro; iSplitL "AU"; iFrame.
    apply prod_update, auth_update, discrete_fun_local_update; intros x; ss.
    destruct (decide (k = x)); subst.
    { rewrite ?discrete_fun_lookup_singleton fn_lookup_insert.
      apply option_local_update, exclusive_local_update; ss.
    }
    { rewrite ?discrete_fun_lookup_singleton_ne; ss.
      apply local_update_discrete; intros [z|] wf Hz; ss; rewrite ?left_id.
      { rewrite left_id in Hz; rewrite -Hz fn_lookup_insert_ne //=. }
      { inv Hz. }
    }
  Qed.

  Definition init_spec : fspec :=
    fspec_simple
      (λ sz : nat,
        (λ varg, ⌜varg = [Vint sz]↑ ∧ (8 * (Z.of_nat sz) < modulus_64)%Z⌝ ∗ pending,
          λ vret, ⌜vret = Vundef↑⌝ ∗ initial_points_tos sz))%I.

  Definition get_spec: fspec :=
    fspec_simple
      (λ '(k, v),
        (λ varg, ⌜varg = [Vint k]↑⌝ ∗ points_to k v,
          λ vret, ⌜vret = (Vint v)↑⌝ ∗ points_to k v))%I.

  Definition set_spec: fspec :=
    fspec_simple
      (λ '(k, w, v),
        (λ varg, ⌜varg = [Vint k; Vint v]↑⌝ ∗ points_to k w,
          λ vret, ⌜vret = Vundef↑⌝ ∗ points_to k v))%I.

  Definition set_by_user_spec: fspec :=
    fspec_simple
      (λ '(k, w),
        (λ varg, ⌜varg = [Vint k]↑⌝ ∗ points_to k w,
          λ vret, ⌜vret = Vundef↑⌝ ∗ ∃ v, points_to k v))%I.

  Definition sp : specmap :=
    {[speckey_fn MapHdr.init := fspec_to_rel init_spec;
      speckey_fn MapHdr.get := fspec_to_rel get_spec;
      speckey_fn MapHdr.set := fspec_to_rel set_spec;
      speckey_fn MapHdr.set_by_user := fspec_to_rel set_by_user_spec]}.

  (*** module A Map
  private map := (fun k => 0)

  def init(sz : int) ≡
    skip

  def get(k : int) : int ≡
    return map[k]

  def set(k : int, v : int) ≡
    map := map[k ← v]

  def set_by_user(k : int) ≡
    set(k, input())
  ***)

  Definition scopes := ["Map"].
  Definition v_map := "Map" ↯ "map".

  Definition set : list val → itree crisE val :=
    λ varg,
      '(k, v): _ <- (pargs [Tint; Tint] varg)!;;
      f <- cgetN v_map;;
      cput v_map (<[k:=v]> (f : Z → Z));;;
      Ret Vundef.

  Definition get : list val → itree crisE val :=
    λ varg,
      k <- (pargs [Tint] varg)!;;
      f <- cgetN v_map;;
      Ret (Vint (f k)).

  Definition set_by_user : list val → itree crisE val :=
    λ varg,
      k <- (pargs [Tint] varg)!;;
      v <- trigger (IO "input" ());;
      ccallN MapHdr.set [Vint k; Vint v].

  Definition fnsems : fnsemmap :=
    {[Some MapHdr.init := Some (msk_scp scopes msk_true, (fsp_some init_spec, fbody_trivial));
      Some MapHdr.get := Some (msk_scp scopes msk_true, (fsp_some get_spec, cfunN get));
      Some MapHdr.set := Some (msk_scp scopes msk_true, (fsp_some set_spec, cfunN set));
      Some MapHdr.set_by_user := Some (msk_scp scopes msk_true, (fsp_some set_by_user_spec, cfunN set_by_user))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_map := Some (λ _ : Z, 0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := (MapA.initial_map ∗ MapM.pending)%I.

  Definition t sp := SMod.to_mod sp smod.
End MapA. End MapA.
