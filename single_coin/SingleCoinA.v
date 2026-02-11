Require Import CRIS.
Require Import SingleCoinHeader.
From iris Require Import gmap_view.

Section RA.
  Context `{!crisG Γ Σ α β τ _I _S}.

  Local Definition CoinRA : ucmra := gmap_viewUR nat (agreeR boolO).
  Class coinG `{!crisG Γ Σ α β τ _I _S} := {
      coin_inG :: inG CoinRA Γ
  }.
  Definition coinΓ : HRA := #[CoinRA].
  Global Instance subG_coinG : subG coinΓ Γ → coinG.
  Proof. solve_inG. Defined.
End RA.
Hint Unfold subG_coinG coin_inG : GRA_index.

Section definitions.
  Context `{_sinvG: !crisG Γ Σ α β τ _I _S}.
  Context `{_coinG: !coinG}.
  
  Definition coin_auth_r (l : list bool) : CoinRA :=
    gmap_view_auth (DfracOwn 1)
      (list_to_map (zip_with (λ a b, (a, b)) (seq 0 (length l)) (map (λ b, to_agree b) l))).
  Definition coin_auth l : iProp Σ := own base_γ (coin_auth_r l).

  Definition coin_r (n : nat) (b : bool) : CoinRA :=
    gmap_view_frag n (DfracOwn 1) (to_agree b).
  Definition coin (n : nat) (b : bool) : iProp Σ :=
    own base_γ (coin_r n b).

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

  Lemma coin_both_valid l n b : coin_auth l -∗ coin n b -∗ ⌜nth_error l n = Some b⌝.
  Proof.
    iIntros "A C"; iCombine "A" "C" gives %WF.
    rewrite /coin_auth_r /coin_r in WF.
    apply gmap_view_both_dfrac_valid_discrete in WF; destruct WF as [? [? [? [EQ ?]]]].
    eapply elem_of_list_to_map in EQ; cycle 1.
    { rewrite fst_zip; [|rewrite length_map length_seq //]. apply NoDup_seq. }
    apply elem_of_lookup_zip_with in EQ; destruct EQ as [? [? [? [EQ ?]]]]; clarify.
    des. apply lookup_seq in H1; des; clarify; ss.
    apply Some_pair_included_r in H2. rewrite Some_included_total in H2.
    apply elem_of_list_split_length in H3. destruct H3 as [l1 [l2 [EQ EQL]]].
    apply map_eq_app in EQ; destruct EQ as [l1' [l2' [-> [EQ1 EQ2]]]].
    destruct l2'; [inv EQ2|ss]. inv EQ2.
    apply to_agree_included in H2; inv H2.
    rewrite length_map. rewrite nth_error_app2 // Nat.sub_diag //.
  Qed.
End definitions.

Module SingleCoinAS. Section SingleCoinAS.
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.
  Context `{_coinG: !coinG}.

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

  Definition sp : alist string fspec :=
    Seal.sealing CRIS
      [(SingleCoinHdr.new, new_spec);
       (SingleCoinHdr.read, read_spec)
      ].
End SingleCoinAS. End SingleCoinAS.

Module SingleCoinA. Section SingleCoinA.
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.
  Context `{_coinG: !coinG}.
  Import SingleCoinAS.

  Definition scopes : list string := [].

  Definition fnsems : fnsems_type :=
    [(Some SingleCoinHdr.new, (true, wmask_all, scopes, (fsp_some new_spec, fbody_trivial)));
     (Some SingleCoinHdr.read, (true, wmask_all, scopes, (fsp_some read_spec, fbody_trivial)))
    ].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp Mod).
End SingleCoinA. End SingleCoinA.
