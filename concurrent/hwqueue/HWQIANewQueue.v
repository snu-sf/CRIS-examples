Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts ProphecyStream.
Require Import HelpingTactics.
Require Import HWQI HWQP SchI HWQA SchTactics.
From stdpp Require Import streams list.

Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mnh mnp : string).
  Context (sp_mem : specmap).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (∃ (X : gset val),
      free_id (λ x, x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type ∗
      [∗ set] x ∈ X, ∃ ptr ofs, ⌜x = Vptr (ptr, ofs)⌝ ∗ ∃ v, (ptr, ofs) ↦{1/2} v)%I.
  Definition IstFull : ist_type Σ := IstHelp_gen Ist mnh ⊤.

  Notation HWQM := (HWQM.t mnh).
  Notation HWQP := (HWQP.t mnp).
  Notation HelpOn := (HelpingOn.t mnh HWQM.jobCode).
  Notation HelpDummy := (HelpingDummy.t mnh).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mnp ∅).

  Lemma simF_new_queue : 
    ISim.sim_fun open
      ((HWQM ★ HelpOn) ★ MemA ★ ProphA) ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
      IstFull (fid HWQHdr.new_queue).
  Proof.
    cStartFunSim. rewrite /HWQA.new_queue /HWQP.new_queue. cStepsS.
    aStepS (N [n sz]) "[-> %Hsz]".
    cStepsT. sYields. 
    mAllocT as (blk) "H"; first by lia.
    replace (Z.to_nat (2 + sz)) with (2 + sz) by lia. s.
    iDestruct "H" as "[sz [back ar]]".
    sYields. mStore. sYields. mStore.
    iRevert "sz"; iIntros "sz". iRevert "back"; iIntros "back". sYields.
    replace sz with ((sz - sz) + sz) at 1 by lia. rewrite replicate_add.
    replace (replicate (sz - sz) Vundef) with (replicate (sz - sz) (Vint 0))
      by rewrite Nat.sub_diag //=.
    rewrite -[X in ITree.iter _ X](Nat.sub_diag sz).
    assert (sz ≤ sz) as Hle by lia; revert Hle.
    generalize sz at 1 4 5 10 as i; intros i Hle.
    iInduction i as [|i] forall (Hle st_src st_tgt).
    { rewrite Nat.sub_0_r /= app_nil_r.
      aUnfoldT. sYields. rewrite Nat2Z.id Nat.ltb_irrefl. cStepsT. sYields.
      iDestruct "IST" as "[% [% [% [% [[-> ->] [[% [HE IST]] ->]]]]]]".
      iDestruct "IST" as "[% [% [-> [HA [%X [free acc]]]]]]".
      destruct (decide (Vptr (blk, 0%Z) ∈ X)) as [HblkX|HblkX].
      { iPoseProof (big_sepS_elem_of_acc with "acc") as "[[% [% [% [% acc]]]] _]"; auto using HblkX.
        clarify. by iPoseProof (mem_points_to_singleton_valid with "acc sz") as "%".
      }
      iDestruct "sz" as "[sz1 sz2]".
      iPoseProof (free_id_split_singleton _ ("hwq", ((Vptr (blk, 0%Z))↑↑)) with "free") as "[tok free]".
      { split; ss. rewrite SAny.upcast_downcast //. }
      cStepsT. iApply (wsim_stream_proph_new (Obs:=nat * bool) with "tok").
      { try solve [simpl_map | prove_inline_cond | prove_sb_cond | ss]. }
      { ss. }
      iIntros (str) "Proph".
      (* invariant construction *)
      iMod new_back as (γb) "Hb●".
      iMod new_back as (γi) "Hi●".
      iMod (new_elts []) as (γe) "[He● He◯]".
      iMod new_no_contra as (γc) "HC".
      iMod new_slots as (γs) "Hs●".
      iMod (hinv_alloc (syn_inv_hwq sz γb γi γe γc γs blk) (n:=n) _ _ N
        with "[ar sz1 back Proph Hb● Hi● He● HC Hs●]") as "#[%γh InvN]"; auto.
      { pose proof (enough_fuel_exists sz ∅ str) as [fuel Hfuel].
        pose (pvs := proph_data fuel sz ∅ str).
        pose (cont := NoCont (map (λ i, (i, [])) pvs)).
        rewrite inv_hwq_red.
        iExists 0, pvs, [], [], cont, ∅, ∅.
        rewrite array_content_empty fmap_empty /=.
        iFrame. iSplitL "ar".
        { iApply (big_sepL_impl with "ar"); iModIntro; iIntros (k?).
          replace (k + 2)%Z with (Z.of_nat (S (S k))) by lia. iIntros "% ? //=".
        }
        repeat (iSplit; first done). iSplit.
        { ss; iPureIntro; ss; esplits; ss; eauto. }
        iSplit; first done. iPureIntro.
        repeat split_and; try done.
        - intros i. split; intros Hi; [ by lia | by inversion Hi].
        - intros e He. set_solver.
        - apply proph_data_NoDup.
        - apply proph_data_sz.
        - intros b. apply initial_block_valid.
        - simpl. apply flatten_blocks_initial. }
      sYieldS. cForceS ((Vptr (blk, 0%Z))↑, tt).
      cIst "IST" with "[- He◯]".
      { iExists _, _, _, _. repeat iSplit; des; eauto.
        iFrame "HE HA". iExists _; iSplitR; first done.
        iExists (X ∪ {[Vptr (blk, 0%Z)]}).
        iSplitL "free".
        { iApply (free_id_iff with "free").
          intros i; case_decide; subst; ss.
          { rewrite SAny.upcast_downcast; split; ss.
            rewrite elem_of_union; intros [_ a]; apply a; right; set_solver+.
          }
          split; intros [? ?]; split; try done.
          { case_match; set_solver. }
          case_match; auto. rewrite elem_of_union; intros [|?%elem_of_singleton].
          { set_solver. }
          subst; destruct i; ss; cSimpl.
        }
        rewrite big_sepS_union; last set_solver.
        iFrame. rewrite big_sepS_singleton; iExists _, _; iSplit; eauto.
      }
      cStep; iFrame "#∗". iModIntro; eauto.
    }
    (* inductive case *)
    aUnfoldT. cStepsT. sYields.
    destruct Nat.ltb eqn : Hltb; first clear Hltb; last first.
    { apply Nat.ltb_ge in Hltb; lia. }
    iPoseProof (big_sepL_insert_acc _ _ (sz - (S i)) with "ar") as "[↦ ar]".
    { rewrite lookup_app_r length_replicate // Nat.sub_diag //=. }
    cStepsT.
    replace (0 + 2 + (sz - S i)%nat)%Z with (Z.of_nat (2 + (sz - S i))) by lia.
    mStore. iPoseProof ("ar" with "↦") as "ar".
    replace (sz - S i) with (length (replicate (sz - S i) (Vint 0)) + 0) at 1
      by (rewrite length_replicate; lia).
    rewrite insert_app_r /=.
    replace (S (sz - S i)) with (sz - i) by lia.
    iApply ("IHi" with "[] IST [ar] sz back"); first (iPureIntro; lia).
    replace (sz - i) with ((sz - S i) + 1) by lia; rewrite replicate_add /=.
    rewrite -(assoc app) //=.
  Qed.
End HWQPM.
