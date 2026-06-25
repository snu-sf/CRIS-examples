Require Import CRIS.
Require Import SingleCoinHeader.
Require Import ProphecyRA.
From iris Require Import gmap_view.

Local Definition CoinRA : ucmra := gmap_viewUR nat (agreeR boolO).
Class coinGpreS `{!crisG Γ Σ α β τ _I _S} := {
  #[local] coin_inG :: inG CoinRA Γ
}.
Class coinGS `{!crisG Γ Σ α β τ _I _S} := {
  #[local] coinGS_coinGpreS :: coinGpreS;
  coin_name : gname;
}.
Definition coinΓ : HRA := #[CoinRA].
Global Instance subG_coinGpreS `{!crisG Γ Σ α β τ _I _S} : subG coinΓ Γ → coinGpreS.
Proof. solve_inG. Defined.

Section definitions.
  Context `{!crisG Γ Σ α β τ _S _I, !coinGS}.

  Definition coin_auth_r (l : list bool) : CoinRA :=
    gmap_view_auth (DfracOwn 1)
      (list_to_map (zip_with (λ a b, (a, b)) (seq 0 (length l)) (map (λ b, to_agree b) l))).
  Definition coin_auth l : iProp Σ := own coin_name (coin_auth_r l).

  Definition coin_r (n : nat) (b : bool) : CoinRA :=
    gmap_view_frag n (DfracOwn 1) (to_agree b).
  Definition coin (n : nat) (b : bool) : iProp Σ :=
    own coin_name (coin_r n b).

  Lemma coin_alloc l b : coin_auth l ==∗ coin_auth (l ++ [b]) ∗ coin (length l) b.
  Proof.
    iIntros "A"; iMod (own_update with "A") as "[A C]"; [|iModIntro; iSplitL "A"; done].
    rewrite /coin_auth_r /coin_r. etrans; first apply (gmap_view_alloc _ (length l) (DfracOwn 1)).
    { eapply not_elem_of_list_to_map. rewrite fst_zip.
      { intros IN; apply elem_of_list_In in IN. apply in_seq in IN; lia. }
      rewrite length_seq length_map //.
    }
    { done. }
    2:{ apply cmra_update_op; [|refl].
      rewrite -list_to_map_snoc.
      { eapply eq_ind; first refl. f_equal. apply map_eq; intros i.
        rewrite length_app /= seq_app /= map_app /= zip_with_app //.
        rewrite length_map length_seq //.
      }
      rewrite fst_zip.
      { intros IN; apply elem_of_list_In in IN. apply in_seq in IN; lia. }
      rewrite length_seq length_map //.
    }
    { ss. }
  Qed.

  Lemma coin_both_valid l n b : coin_auth l -∗ coin n b -∗ ⌜l !! n = Some b⌝.
  Proof.
    iIntros "A C"; iCombine "A" "C" gives %WF.
    rewrite /coin_auth_r /coin_r in WF.
    apply gmap_view_both_dfrac_valid_discrete in WF; destruct WF as [? [? [? [EQ [Hwf1 Hwf2]]]]].
    eapply elem_of_list_to_map in EQ; cycle 1.
    { rewrite fst_zip; [|rewrite length_map length_seq //]. apply NoDup_seq. }
    apply elem_of_lookup_zip_with in EQ; destruct EQ as [? [? [? [EQ [Heq1 Heq2]]]]]; clarify.
    apply lookup_seq in Heq1; des; clarify; ss.
    apply Some_pair_included_r in Hwf2. rewrite Some_included_total in Hwf2.
    apply elem_of_list_split_length in Heq2. destruct Heq2 as [l1 [l2 [EQ EQL]]].
    apply map_eq_app in EQ; destruct EQ as [l1' [l2' [-> [EQ1 EQ2]]]].
    destruct l2'; [inv EQ2|ss]. inv EQ2.
    apply to_agree_included in Hwf2; inv Hwf2.
    rewrite length_map. rewrite lookup_app_r // Nat.sub_diag //.
  Qed.
End definitions.

Module SingleCoinA. Section SingleCoinA.
  Context `{!crisG Γ Σ α β τ _S _I, !coinGS, !prophGS}.

  Definition new_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ varg, ⌜varg = tt↑⌝),
      (λ vret, ∃ n b, ⌜vret = n↑⌝ ∗ coin n b))
    )%I.

  Definition read_spec : fspec :=
    fspec_simple (λ '(n, b),
      ((λ varg, ⌜varg = n↑⌝ ∗ coin n b),
      (λ vret, ⌜vret = b↑⌝ ∗ coin n b))
    )%I.

  Definition scopes : list string := [].

  Definition fnsems : fnsemmap :=
    {[fid SingleCoinHdr.new  # (msk_scp scopes msk_true, (fsp_some new_spec, fbody_trivial));
      fid SingleCoinHdr.read # (msk_scp scopes msk_true, (fsp_some read_spec, fbody_trivial))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ :=
    coin_auth nil ∗
    ProphecyRA.free_id (λ i, i.1 = "SingleCoin" ∧ ∃ n, i.2↓↓ = Some n ∧ n >= 0)%type.

  Definition t sp : Mod.t := SMod.to_mod sp Mod.
End SingleCoinA. End SingleCoinA.
