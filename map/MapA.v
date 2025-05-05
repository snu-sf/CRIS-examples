Require Import CRIS.

Require Import MapHeader MapM.

Set Implicit Arguments.

(* Resource algebra for MapM ⊆ MapA *)
Section RA.
  Context `{!sinvG Γ Σ α β τ _I _S}.

  Local Definition RA : ucmra :=
    prodUR (optionUR (exclR unitO)) (authUR (Z -d> optionUR (exclR ZO))).

  Class mapG `{!sinvG Γ Σ α β τ _I _S} := {
      map_inG :: inG RA Γ
    }.
  Definition mapΓ : HRA := #[RA].
  Global Instance subG_mapG : subG mapΓ Γ → mapG.
  Proof. solve_inG. Defined.
End RA.  
Hint Unfold subG_mapG map_inG : GRA_index.

Module MapAS. Section MapAS.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_mapMG: !mapMG}.
  Context `{_mapG: !mapG}.

  Definition pending : iProp Σ := own base_γ (Some (Excl ()), ε).

  Local Definition initial_fun : Z -d> optionUR (exclR ZO) := λ z, Some (Excl 0%Z).
  Definition initial_map : iProp Σ := own base_γ (ε, ● initial_fun ⋅ ◯ initial_fun).

  Definition auth_allocated (f : Z → Z) : iProp Σ :=
    own base_γ (ε, ● ((λ k, Some (Excl (f k))) : Z -d> optionUR (exclR ZO))).
  Definition auth_unallocated (sz : Z) : iProp Σ :=
    own base_γ
      (ε,
      ◯ ((λ k,
        if (Z_gt_le_dec 0 k)
        then Some (Excl 0%Z)
        else if (Z_gt_le_dec sz k) then ε else Some (Excl 0%Z)) : Z -d> optionUR (exclR ZO)))%Z.
  Definition points_to (k v : Z) : iProp Σ :=
    own base_γ (ε, ◯ (discrete_fun_singleton k (Some (Excl v)))).
  Definition initial_points_tos (sz : nat) : iProp Σ :=
    ([∗ list] i↦v ∈ (repeat (0 : Z) sz), points_to i%Z v)%I.

  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof.
    iIntros "P P'"; iCombine "P P'" as "P" gives %FALSE.
    rewrite -pair_op pair_valid in FALSE; des; ss.
  Qed.
  Lemma initialize (sz : nat) :
    initial_map ==∗ auth_allocated (λ _ : Z, 0%Z) ∗ auth_unallocated sz ∗ initial_points_tos sz.
  Proof.
    induction sz; ss.
    { rewrite /initial_map /initial_fun /auth_allocated /auth_unallocated /initial_points_tos; unseal "MapAS".
      iIntros "[I1 I2]"; iSplitL "I1"; first iModIntro; iFrame.
      iSplitL; last iModIntro; ss; iApply (own_update with "I2").
      apply prod_update; ss.
      rewrite cmra_update_proper; try reflexivity.
      f_equiv. ii; des_ifs; lia.
    }
    { iIntros "I"; iMod (IHsz with "I") as "[I1 [I2 I3]]".
      rewrite /initial_map /initial_fun /auth_allocated /auth_unallocated /initial_points_tos; unseal "MapAS".
      replace (S sz) with (sz + 1); last by lia.
      rewrite repeat_app big_opL_app repeat_length; ss.
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
  Proof.
    rewrite /initial_map /points_to /initial_fun; unseal "MapAS".
    iIntros "[I1 I2] PT"; iCombine "I2" "PT" as "I" gives %FALSE.
    rewrite -pair_op pair_valid /= -auth_frag_op auth_frag_valid in FALSE.
    destruct FALSE as [_ FALSE]. specialize (FALSE k); ss.
    rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton //= in FALSE.
  Qed.
  Lemma auth_unallocated_points_to sz k v : auth_unallocated sz -∗ points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
  Proof.
    rewrite /auth_unallocated /points_to; unseal "MapAS".
    iIntros "I PT"; iCombine "I" "PT" as "I" gives %wf.
    rewrite -pair_op pair_valid /= -auth_frag_op auth_frag_valid in wf.
    destruct wf as [_ wf]. specialize (wf k); ss.
    rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton //= in wf.
    des_ifs; ss. iPureIntro; lia.
  Qed.
  Lemma auth_allocated_get f k v : auth_allocated f -∗ points_to k v -∗ ⌜f k = v⌝.
  Proof.
    rewrite /auth_allocated /points_to; unseal "MapAS".
    iIntros "A P"; iCombine "A" "P" as "A" gives %wf.
    rewrite -pair_op pair_valid auth_both_valid_discrete /= in wf; des.
    apply (discrete_fun_included_spec_1 _ _ k) in wf0; ss; rewrite discrete_fun_lookup_singleton in wf0.
    rewrite Excl_included in wf0; inv wf0; ss.
  Qed.
  Lemma auth_allocated_set f k v w :
    auth_allocated f -∗ points_to k w ==∗ auth_allocated (<[k := v]> f) ∗ points_to k v.
  Proof.
    rewrite /auth_allocated /points_to; unseal "MapAS".
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

  Section spec.
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
    
    Definition sp : alist string fspec :=
      Seal.sealing CRIS
        [(MapHdr.init, init_spec);
        (MapHdr.get, get_spec);
        (MapHdr.set, set_spec);
        (MapHdr.set_by_user, set_by_user_spec)].
    
    Lemma sp_nodup : List.NoDup (List.map fst sp).
    Proof. unfold sp. unseal CRIS. prove_nodup. Qed.
  End spec.
End MapAS. End MapAS.

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

Module MapA. Section MapA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_mapMG: !mapMG}.
  Context `{_mapG: !mapG}.

  Definition scopes := ["Map"].
  Definition v_map := "Map" ↯ "map".

  Definition set : list val → itree hmodE val :=
    λ varg,
      '(k, v): _ <- (pargs [Tint; Tint] varg)!;;
      f <- cgetN v_map;;
      cput v_map (<[k:=v]> (f : Z → Z));;;
      Ret Vundef.

  Definition get : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)!;;
      f <- cgetN v_map;;
      Ret (Vint (f k)).

  Definition set_by_user : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)!;;
      v <- trigger (IO "input" ());;
      ccallN MapHdr.set [Vint k; Vint v].

  Definition fnsems :=
    [(MapHdr.init, (wmask_all, scopes, mk_specbody MapAS.init_spec fbody_trivial));
     (MapHdr.get, (wmask_all, scopes, mk_specbody MapAS.get_spec (cfunN get)));
     (MapHdr.set, (wmask_all, scopes, mk_specbody MapAS.set_spec (cfunN set)));
     (MapHdr.set_by_user, (wmask_all, scopes, mk_specbody MapAS.set_by_user_spec (cfunN set_by_user)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_map, (λ _ : Z, 0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ :=
    (MapAS.initial_map ∗ MapMS.pending)%I.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod sp Mod).
End MapA. End MapA.
