Require Import CRIS.
Require Export SingleCoinHeader SingleCoinP SingleCoinA.
Require Export ProphecyHeader ProphecyA.

Local Program Definition coin_proph : Prophecy.t := {|
  Prophecy.Pro := bool;
  Prophecy.Obs := bool;
  Prophecy.consistent := λ l p, l = [] ∨ ∃ tl, l = tl ++ [p];
  Prophecy.obs_default := true;
|}.
Next Obligation.
  intros seq; exists (seq 0); intros i; induction i.
  { left; ss. }
  { right; ss. destruct i; s; [exists nil; ss|]. destruct IHi as [H|H]; [inv H|].
    destruct H as [tl H].
    exists (seq (S i) :: tl); ss; rewrite H; ss.
  }
Qed.

Module SingleCoinPA. Section SingleCoinPA.
  Import SingleCoinA SingleCoinP.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _PROPH: !prophGS, _COIN: !coinGS}.
  Context (mn : string) (sp : specmap).

  Local Notation MA := (SingleCoinA.t sp).
  Local Notation MI := (SingleCoinP.t mn ★ ProphecyA.t mn ∅).

  Local Definition Ist : ist_type Σ :=
    (λ st_s st_t,
      ∃ (l_s : list bool) (l_t : list (option bool)),
        ⌜st_t = {[v_coins := Some l_t↑]} ∧ length l_s = length l_t⌝
        ∗ ProphecyRA.free_id (λ i, i.1 = "SingleCoin" ∧ ∃ n, i.2↓↓ = Some n ∧ n >= length l_t)%type
        ∗ coin_auth l_s
        ∗ [∗ list] i ↦ ob ∈ l_t,
          ∃ b ol, ProphecyRA.has_proph (proph_coins i) (existT coin_proph (b, ol))
          ∗ ⌜l_s !! i = Some b
            ∧ (match ob with Some b' => b' = b ∧ ol = [b] | None => ol = [] end)
            ∧ (Prophecy.consistent coin_proph ol b)⌝
        )%I.

  Lemma simF_new : ISim.sim_fun open MA MI Ist (Some SingleCoinHdr.new).
  Proof.
    iStartSim.
    iDestruct "IST" as (l_s l_t) "[[-> %EQ] [F [AUTH PL]]]".
    steps_l. iDestruct "ASM" as "[-> ->]". hss.

    steps_r. inline_r. force_r (proph_coins (length l_t), coin_proph).
    steps_r. force_r ((proph_coins (length l_t))↑). steps_r.
    iPoseProof (ProphecyRA.free_id_split _ (proph_coins (length l_t)) with "F") as "> [F1 F2]".
    { ss; hss; esplits; eauto. }
    force_r; iFrame; iSplit; eauto.
    steps_r. iDestruct "GRT" as "[-> [%b [-> P]]]". steps_r.

    (* alloc coin *)
    iMod (coin_alloc _ b with "AUTH") as "[AUTH COIN]".
    iIst "IST" with "[F2 PL P AUTH]".
    { iExists (l_s ++ [b]), (l_t ++ [None]). iSplit; eauto.
      { iPureIntro; splits; ss; eauto. rewrite ?length_app; s; lia. }
      iSplitL "F2".
      { iApply ProphecyRA.free_id_iff; [|iFrame].
        intros [name a]; split; ss; des_ifs.
        { intros t; inv t; des; clarify. inv e. hss. rewrite length_app in H1. ss. lia. }
        { intros t; des; esplits; eauto. rewrite length_app in t1; ss; lia. }
        { intros [-> [n0 [EQ' GT]]]; esplits; eauto.
          assert (n0 <> length l_t).
          { ii; clarify; eapply n; rewrite /proph_coins; f_equal. hexploit SAny.downcast_upcast; eauto. }
          rewrite length_app; ss; lia.
        }
      }
      iFrame.
      iApply (big_sepL_app). iSplitL "PL"; cycle 1.
      { s. iSplit; [|done]. iExists b, []; iSplit.
        { rewrite Nat.add_0_r; iFrame. }
        iPureIntro. rewrite -EQ.
        rewrite lookup_app_r; [|lia].
        rewrite Nat.add_comm /= Nat.sub_diag /=.
        esplits; eauto.
      }
      iApply (big_sepL_impl with "PL").
      iModIntro; iIntros (k x) "% [%b' [%ol' H]]".
      apply lookup_lt_Some in H; rewrite -EQ in H.
      rewrite lookup_app_l //.
      iExists _, _; iFrame.
    }

    forces_l. iFrame. iSplit; eauto.
    step. iFrame. eauto.
  Qed.

  Lemma simF_read : ISim.sim_fun open MA MI Ist (Some SingleCoinHdr.read).
  Proof.
    iStartSim.
    steps_l. destruct _q as [idx b]. iDestruct "ASM" as "[-> [-> C]]".
    iDestruct "IST" as (l_s l_t) "[[-> %EQ] [F [AU PL]]]".
    iPoseProof (coin_both_valid with "AU C") as "%NTH".

    steps_r.
    assert (idx < length l_s) by (eapply lookup_lt_Some; eauto).
    destruct (l_t !! idx) as [o|] eqn : LTN; cycle 1.
    { apply lookup_ge_None in LTN; lia. }
    destruct o as [bn'|].
    { (* after initialization *)
      iPoseProof (big_sepL_lookup_acc _ _ idx with "PL") as "[P PL]"; eauto.
      iDestruct "P" as "[%bn [%oln [P %P]]]".
      rewrite NTH in P. rewrite NTH. destruct P as [NTH' [EQ' ?]].
      hexploit EQ'; ss; i; des; clarify.
      forces_l. iFrame. iSplit; eauto.
      step. iSplit; eauto.
      iFrame. iSplit; eauto. iApply "PL". iExists _, _; iFrame.
      iPureIntro; splits; ss. right; esplits; eauto.
    }
    { (* before initialization *)
      eapply elem_of_list_split_length in LTN; destruct LTN as [l1 [l2 [-> ->]]].
      steps_r. rewrite take_app Nat.sub_diag /= app_nil_r firstn_all drop_app.
      rewrite drop_ge; [|lia]; rewrite /= Nat.sub_succ_l // Nat.sub_diag /= drop_0.
      iPoseProof (big_sepL_app with "PL") as "[PL1 [P PL2]]".
      iDestruct "P" as "[%bn [%oln [P %HP]]]".
      inline_r. force_r (proph_coins _, existT coin_proph (_, _, _)). forces_r. iFrame.
      rewrite Nat.add_0_r. iSplit; eauto.
      steps_r. iDestruct "GRT" as "[-> [[-> %GRT] P]]". steps_r.
      destruct GRT as [|[tl EQ']]; [clarify|].
      destruct tl; cycle 1.
      { inv EQ'. destruct HP as [? [Htemp ?]]. exfalso; eapply app_cons_not_nil; eauto. }
      inv EQ'.

      forces_l. iFrame. iSplit; eauto. step.
      rewrite Nat.add_0_r NTH in HP; destruct HP as [? [_ HP]]; clarify.
      iSplit; eauto.
      iExists l_s, _. iSplit; [iPureIntro; splits; eauto|].
      { rewrite EQ ?length_app /= //. }
      iSplitL "F".
      { iApply ProphecyRA.free_id_iff; ss. rewrite ?length_app //. }
      iFrame.
      iExists bn, [bn]; rewrite Nat.add_0_r. iFrame.
      iPureIntro; ss; esplits; eauto. right; exists []; eauto.
    }
  Qed.

  Lemma sim : ISim.t open MA MI SingleCoinA.init_cond Ist.
  Proof.
    init_sim.
    { iIntros "[A F]". iExists [], []. iSplit; eauto. iFrame. ss. }
    { eapply simF_new; eauto. }
    { eapply simF_read; eauto. }
  Qed.
End SingleCoinPA. End SingleCoinPA.
